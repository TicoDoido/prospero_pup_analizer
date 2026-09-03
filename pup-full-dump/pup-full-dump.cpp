#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <cstddef>
#include <cstring>
#include <cstdarg>
#include <cerrno>
#include <algorithm>
#include <limits>
#include <climits>

#include <fcntl.h>
#include <unistd.h>
#include <sys/ioctl.h>
#include <sys/stat.h>
#include <sys/types.h>

#ifndef HOST_TEST
extern "C" {
#include <ps5/kernel.h>
}
#else
static inline uint64_t kernel_get_ucred_authid(pid_t) { return 0; }
static inline uint32_t kernel_get_fw_version() { return 0; }
static inline int kernel_set_ucred_authid(pid_t, uint64_t) { return 0; }
static inline void* kernel_get_root_vnode() { return nullptr; }
static inline int kernel_set_proc_rootdir(pid_t, void*) { return 0; }
#endif

static constexpr uint32_t BLS_MAGIC = 0x32424C53;
static constexpr uint32_t PUP_MAGIC = 0xEEF51454;
static constexpr size_t BLS_HEADER_READ = 0x400;
static constexpr size_t ALIGNMENT = 0x4000;

static const char* INPUT_CANDIDATES[] = {
    "/mnt/usb0/PROSPERO/UPDATE/PROSPEROUPDATE.PUP",
    "/mnt/usb0/PS5UPDATE.PUP",
    "/mnt/usb0/PROSPEROUPDATE.PUP",
};

static const char* OUTPUT_DIR = "/mnt/usb0/pup_dump";
static const char* LOG_PATH   = "/mnt/usb0/pup_dump/pup_dump.log";

#pragma pack(push, 1)
struct BlsEntry {
    uint32_t block_offset;
    uint32_t size;
    uint8_t reserved[8];
    char name[32];
};

struct BlsHeader {
    uint32_t magic;
    uint32_t version;
    uint32_t flags;
    uint32_t file_count;
    uint32_t block_count;
    uint8_t unknown[12];
    BlsEntry entry_list[0];
};

struct PupFileHeader {
    uint32_t magic;
    uint32_t unknown_04;
    uint16_t unknown_08;
    uint8_t flags;
    uint8_t unknown_0B;
    uint16_t unknown_0C;
    uint16_t unknown_0E;
};

struct PupHeader {
    PupFileHeader file_header;
    uint64_t file_size;
    uint16_t segment_count;
    uint16_t unknown_1A;
    uint32_t unknown_1C;
};

struct PupSegment {
    uint32_t flags;
    uint32_t flags2;
    int64_t offset;
    uint64_t compressed_size;
    uint64_t uncompressed_size;
};

struct PupBlockInfo {
    uint32_t offset;
    uint32_t size;
};
#pragma pack(pop)

// Layouts consumed by /dev/pup_update0.
struct VerifyBlsHeaderArgs {
    void* buffer;
    unsigned long length;
    unsigned long unknown;
};

struct DecryptHeaderArgs {
    void* buffer;
    size_t length;
    int type;
};

struct VerifySegmentArgs {
    uint16_t index;
    void* buffer;
    size_t length;
};

struct DecryptSegmentArgs {
    uint16_t index;
    void* buffer;
    size_t length;
};

struct DecryptSegmentBlockArgs {
    uint16_t entry_index;
    uint16_t block_index;
    void* block_buffer;
    size_t block_length;
    void* table_buffer;
    size_t table_length;
};

static FILE* g_log = nullptr;
static FILE* g_manifest = nullptr;

static void logf(const char* fmt, ...) {
    va_list ap;
    va_start(ap, fmt);
    va_list copy;
    va_copy(copy, ap);
    std::vprintf(fmt, ap);
    std::fflush(stdout);
    if (g_log) {
        std::vfprintf(g_log, fmt, copy);
        std::fflush(g_log);
    }
    va_end(copy);
    va_end(ap);
}

static void hexdump_prefix(const char* label, const uint8_t* p, size_t n) {
    const size_t shown = std::min<size_t>(n, 64);
    logf("%s (%zu bytes shown):", label, shown);
    for (size_t i = 0; i < shown; ++i) {
        if ((i % 16) == 0) logf("\n  ");
        logf("%02X ", p[i]);
    }
    logf("\n");
}

static void* alloc_aligned(size_t size) {
    void* p = nullptr;
    if (posix_memalign(&p, ALIGNMENT, std::max<size_t>(size, 1)) != 0) return nullptr;
    std::memset(p, 0, size);
    return p;
}

static bool pread_exact(int fd, uint64_t off, void* buf, size_t size) {
    uint8_t* p = static_cast<uint8_t*>(buf);
    size_t done = 0;
    while (done < size) {
        ssize_t r = pread(fd, p + done, size - done, static_cast<off_t>(off + done));
        if (r <= 0) return false;
        done += static_cast<size_t>(r);
    }
    return true;
}

static bool write_exact_at(int fd, uint64_t off, const void* data, size_t size) {
    const uint8_t* p = static_cast<const uint8_t*>(data);
    size_t done = 0;
    while (done < size) {
        ssize_t w = pwrite(fd, p + done, size - done,
                           static_cast<off_t>(off + done));
        if (w <= 0) return false;
        done += static_cast<size_t>(w);
    }
    return true;
}

static bool path_exists(const char* path) {
    return path && *path && access(path, F_OK) == 0;
}

// Never overwrite an older extraction.  "foo.ext" becomes "foo_1.ext",
// "foo_2.ext", ... .  The counter is inserted before the final extension.
// With also_check_partial=true, "candidate.partial" is considered occupied too.
static bool make_unique_path(char* path, size_t cap, bool also_check_partial = false) {
    if (!path || cap < 2 || !*path) return false;

    char original[512]{};
    const int copied = std::snprintf(original, sizeof(original), "%s", path);
    if (copied <= 0 || static_cast<size_t>(copied) >= sizeof(original)) return false;

    auto occupied = [also_check_partial](const char* candidate) -> bool {
        if (path_exists(candidate)) return true;
        if (!also_check_partial) return false;
        char partial[640]{};
        const int n = std::snprintf(partial, sizeof(partial), "%s.partial", candidate);
        if (n <= 0 || static_cast<size_t>(n) >= sizeof(partial)) return true;
        return path_exists(partial);
    };

    if (!occupied(original)) return true;

    const char* slash = std::strrchr(original, '/');
    const char* base = slash ? slash + 1 : original;
    const char* dot = std::strrchr(base, '.');
    const size_t prefix_len = dot ? static_cast<size_t>(dot - original) : std::strlen(original);
    const char* extension = dot ? dot : "";

    for (unsigned n = 1; n < 100000; ++n) {
        const int written = std::snprintf(path, cap, "%.*s_%u%s",
                                          static_cast<int>(prefix_len), original, n, extension);
        if (written <= 0 || static_cast<size_t>(written) >= cap) return false;
        if (!occupied(path)) return true;
    }
    return false;
}

static int create_output_file(const char* path, uint64_t final_size) {
    if (final_size > static_cast<uint64_t>(std::numeric_limits<off_t>::max())) {
        logf("[!] Output file is too large for off_t: %s\n", path);
        return -1;
    }
    // O_EXCL is the last line of defense against accidental overwrites.
    int fd = open(path, O_WRONLY | O_CREAT | O_EXCL, 0666);
    if (fd < 0) {
        logf("[!] open(%s) failed: errno=%d (%s)\n", path, errno, strerror(errno));
        return -1;
    }
    if (ftruncate(fd, static_cast<off_t>(final_size)) != 0) {
        logf("[!] ftruncate(%s, 0x%llX) failed: errno=%d (%s)\n", path,
             static_cast<unsigned long long>(final_size), errno, strerror(errno));
        close(fd);
        unlink(path);
        return -1;
    }
    return fd;
}

// Exact per-block decision used by the Safe Mode PupReader.  A segment may be
// block-compressed (flags & 8) while individual incompressible blocks are kept
// RAW.  The low bits in PupBlockInfo::size encode padding/alignment metadata.
struct BlockReadPlan {
    size_t read_size;
    bool compressed;
};

static bool block_read_plan(const PupBlockInfo& info, uint32_t flags2,
                            uint64_t segment_size, size_t block_size,
                            size_t expected_size, bool is_last,
                            BlockReadPlan* plan) {
    if (!plan || block_size == 0 || expected_size == 0) return false;

    const uint32_t mask = (flags2 & 1) ? 0x1ffu : 0x0fu;
    const uint32_t clear_mask = ~mask;
    const uint32_t encoded_size = info.size;
    const uint32_t aligned_size = encoded_size & clear_mask;
    const uint32_t low_tag = encoded_size & mask;
    const uint32_t unpadded_size = aligned_size - low_tag;

    size_t read_size = 0;
    bool compressed = true;

    // Safe Mode has a special rule for the short tail block.
    if (is_last && expected_size < block_size && encoded_size == expected_size) {
        read_size = expected_size;
        compressed = false;
    } else if (unpadded_size == block_size) {
        read_size = block_size;
        compressed = false;
    } else {
        read_size = aligned_size;
        compressed = true;
    }

    if (read_size == 0 || read_size > static_cast<size_t>(std::numeric_limits<ssize_t>::max()) ||
        info.offset > segment_size || read_size > segment_size - info.offset)
        return false;

    plan->read_size = read_size;
    plan->compressed = compressed;
    return true;
}

// Minimal, bounded RFC 1950/1951 inflater.  Keeping it in the payload avoids
// a dependency on libz, which is not part of ps5-payload-dev/sdk.
static constexpr int INFLATE_OK = 0;
static constexpr int INFLATE_DATA_ERROR = -1;
static constexpr int INFLATE_BUF_ERROR = -2;

struct BitReader {
    const uint8_t* data;
    size_t size;
    size_t pos;
    uint64_t bits;
    unsigned count;

    BitReader(const uint8_t* p, size_t n) : data(p), size(n), pos(0), bits(0), count(0) {}

    void fill(unsigned want) {
        while (count < want && pos < size) {
            bits |= static_cast<uint64_t>(data[pos++]) << count;
            count += 8;
        }
    }
    bool read(unsigned n, uint32_t* value) {
        fill(n);
        if (count < n) return false;
        *value = static_cast<uint32_t>(bits & ((1ULL << n) - 1));
        bits >>= n;
        count -= n;
        return true;
    }
    void align_byte() {
        const unsigned n = count & 7;
        bits >>= n;
        count -= n;
    }
};

static uint16_t reverse_bits(uint16_t value, unsigned n) {
    uint16_t result = 0;
    while (n--) { result = static_cast<uint16_t>((result << 1) | (value & 1)); value >>= 1; }
    return result;
}

struct Huffman {
    uint32_t table[1 << 15];

    bool build(const uint8_t* lengths, unsigned symbols) {
        uint16_t counts[16]{};
        uint16_t next[16]{};
        uint32_t code = 0;
        bool any = false;
        std::memset(table, 0, sizeof(table));
        for (unsigned i = 0; i < symbols; ++i) {
            if (lengths[i] > 15) return false;
            if (lengths[i]) { ++counts[lengths[i]]; any = true; }
        }
        if (!any) return false;
        for (unsigned len = 1; len <= 15; ++len) {
            code = (code + counts[len - 1]) << 1;
            next[len] = static_cast<uint16_t>(code);
        }
        for (unsigned symbol = 0; symbol < symbols; ++symbol) {
            const unsigned len = lengths[symbol];
            if (!len) continue;
            const uint16_t reversed = reverse_bits(next[len]++, len);
            const uint32_t packed = (len << 16) | symbol;
            const uint32_t step = 1u << len;
            for (uint32_t i = reversed; i < (1u << 15); i += step) table[i] = packed;
        }
        return true;
    }

    bool decode(BitReader* reader, unsigned* symbol) const {
        reader->fill(15);
        if (!reader->count) return false;
        const uint32_t packed = table[static_cast<uint32_t>(reader->bits) & 0x7fff];
        const unsigned len = packed >> 16;
        if (!len || reader->count < len) return false;
        reader->bits >>= len;
        reader->count -= len;
        *symbol = packed & 0xffff;
        return true;
    }
};

static bool fixed_tables(Huffman* litlen, Huffman* distance) {
    uint8_t lit_lengths[288]{};
    uint8_t dist_lengths[32]{};
    for (unsigned i = 0; i <= 143; ++i) lit_lengths[i] = 8;
    for (unsigned i = 144; i <= 255; ++i) lit_lengths[i] = 9;
    for (unsigned i = 256; i <= 279; ++i) lit_lengths[i] = 7;
    for (unsigned i = 280; i <= 287; ++i) lit_lengths[i] = 8;
    for (unsigned i = 0; i < 32; ++i) dist_lengths[i] = 5;
    return litlen->build(lit_lengths, 288) && distance->build(dist_lengths, 32);
}

static bool dynamic_tables(BitReader* reader, Huffman* litlen, Huffman* distance) {
    static const uint8_t order[19] = {16,17,18,0,8,7,9,6,10,5,11,4,12,3,13,2,14,1,15};
    uint32_t value = 0;
    if (!reader->read(5, &value)) return false;
    const unsigned nlit = value + 257;
    if (!reader->read(5, &value)) return false;
    const unsigned ndist = value + 1;
    if (!reader->read(4, &value)) return false;
    const unsigned ncode = value + 4;
    uint8_t code_lengths[19]{};
    for (unsigned i = 0; i < ncode; ++i) {
        if (!reader->read(3, &value)) return false;
        code_lengths[order[i]] = static_cast<uint8_t>(value);
    }
    Huffman code_tree;
    if (!code_tree.build(code_lengths, 19)) return false;
    uint8_t lengths[320]{};
    const unsigned total = nlit + ndist;
    for (unsigned i = 0; i < total;) {
        unsigned symbol = 0;
        if (!code_tree.decode(reader, &symbol)) return false;
        if (symbol < 16) {
            lengths[i++] = static_cast<uint8_t>(symbol);
            continue;
        }
        unsigned repeat = 0;
        uint8_t repeated = 0;
        if (symbol == 16) {
            if (!i || !reader->read(2, &value)) return false;
            repeat = value + 3;
            repeated = lengths[i - 1];
        } else if (symbol == 17) {
            if (!reader->read(3, &value)) return false;
            repeat = value + 3;
        } else if (symbol == 18) {
            if (!reader->read(7, &value)) return false;
            repeat = value + 11;
        } else {
            return false;
        }
        if (repeat > total - i) return false;
        while (repeat--) lengths[i++] = repeated;
    }
    return litlen->build(lengths, nlit) && distance->build(lengths + nlit, ndist);
}

static int inflate_codes(BitReader* reader, const Huffman& litlen, const Huffman& distance,
                         uint8_t* output, size_t capacity, size_t* position) {
    static const uint16_t length_base[29] = {3,4,5,6,7,8,9,10,11,13,15,17,19,23,27,31,35,
                                              43,51,59,67,83,99,115,131,163,195,227,258};
    static const uint8_t length_extra[29] = {0,0,0,0,0,0,0,0,1,1,1,1,2,2,2,2,3,3,3,3,
                                              4,4,4,4,5,5,5,5,0};
    static const uint16_t distance_base[30] = {1,2,3,4,5,7,9,13,17,25,33,49,65,97,129,193,
                                                257,385,513,769,1025,1537,2049,3073,4097,6145,
                                                8193,12289,16385,24577};
    static const uint8_t distance_extra[30] = {0,0,0,0,1,1,2,2,3,3,4,4,5,5,6,6,7,7,8,8,
                                                9,9,10,10,11,11,12,12,13,13};
    for (;;) {
        unsigned symbol = 0;
        if (!litlen.decode(reader, &symbol)) return INFLATE_DATA_ERROR;
        if (symbol < 256) {
            if (*position == capacity) return INFLATE_BUF_ERROR;
            output[(*position)++] = static_cast<uint8_t>(symbol);
            continue;
        }
        if (symbol == 256) return INFLATE_OK;
        if (symbol < 257 || symbol > 285) return INFLATE_DATA_ERROR;
        const unsigned length_index = symbol - 257;
        uint32_t value = 0;
        if (!reader->read(length_extra[length_index], &value)) return INFLATE_DATA_ERROR;
        const size_t length = length_base[length_index] + value;
        unsigned dist_symbol = 0;
        if (!distance.decode(reader, &dist_symbol) || dist_symbol >= 30 ||
            !reader->read(distance_extra[dist_symbol], &value)) return INFLATE_DATA_ERROR;
        const size_t back = distance_base[dist_symbol] + value;
        if (!back || back > *position || length > capacity - *position) return INFLATE_DATA_ERROR;
        for (size_t i = 0; i < length; ++i) {
            const uint8_t byte = output[*position - back];
            output[*position] = byte;
            ++(*position);
        }
    }
}

static int inflate_block(const uint8_t* input, size_t input_size,
                         uint8_t* output, size_t output_capacity,
                         size_t* output_size) {
    if (!input || !output || !output_size || input_size < 2) return INFLATE_DATA_ERROR;
    const uint16_t header = static_cast<uint16_t>((input[0] << 8) | input[1]);
    if ((input[0] & 0x0f) != 8 || (input[0] >> 4) > 7 || header % 31 || (input[1] & 0x20))
        return INFLATE_DATA_ERROR;
    BitReader reader(input + 2, input_size - 2);
    size_t position = 0;
    for (;;) {
        uint32_t final = 0, type = 0;
        if (!reader.read(1, &final) || !reader.read(2, &type)) return INFLATE_DATA_ERROR;
        if (type == 0) {
            reader.align_byte();
            uint32_t length = 0, complement = 0;
            if (!reader.read(16, &length) || !reader.read(16, &complement) ||
                static_cast<uint16_t>(length) != static_cast<uint16_t>(~complement) ||
                length > output_capacity - position) return INFLATE_DATA_ERROR;
            for (uint32_t i = 0, byte = 0; i < length; ++i) {
                if (!reader.read(8, &byte)) return INFLATE_DATA_ERROR;
                output[position++] = static_cast<uint8_t>(byte);
            }
        } else {
            Huffman litlen, distance;
            const bool valid = type == 1 ? fixed_tables(&litlen, &distance) :
                               type == 2 ? dynamic_tables(&reader, &litlen, &distance) : false;
            if (!valid) return INFLATE_DATA_ERROR;
            const int ret = inflate_codes(&reader, litlen, distance, output, output_capacity, &position);
            if (ret != INFLATE_OK) return ret;
        }
        if (final) { *output_size = position; return INFLATE_OK; }
    }
}

static int translate_type(int type) {
    switch (type) {
        case 0: case 3: return 0;
        case 1: case 4: return 1;
        case 2: case 5: return 2;
        default: return 0;
    }
}

static int ioctl_verify_bls(int fd, void* buffer, size_t length) {
    VerifyBlsHeaderArgs a{};
    a.buffer = buffer;
    a.length = length;
    a.unknown = 0;
    errno = 0;
    return ioctl(fd, 0xC0104401, &a);
}

static int ioctl_decrypt_header(int fd, void* buffer, size_t length, int type) {
    DecryptHeaderArgs a{};
    a.buffer = buffer;
    a.length = length;
    a.type = translate_type(type);
    errno = 0;
    return ioctl(fd, 0xC0184402, &a);
}

static int ioctl_verify_segment(int fd, uint16_t index, void* buffer, size_t length, bool additional) {
    VerifySegmentArgs a{};
    a.index = index;
    a.buffer = buffer;
    a.length = length;
    errno = 0;
    return ioctl(fd, additional ? 0xC0184403 : 0xC0184404, &a);
}

static int ioctl_decrypt_segment(int fd, uint16_t index, void* buffer, size_t length) {
    DecryptSegmentArgs a{};
    a.index = index;
    a.buffer = buffer;
    a.length = length;
    errno = 0;
    return ioctl(fd, 0xC0184405, &a);
}

static int ioctl_decrypt_block(int fd, uint16_t entry_index, uint16_t block_index,
                               void* block_buffer, size_t block_length,
                               void* table_buffer, size_t table_length) {
    DecryptSegmentBlockArgs a{};
    a.entry_index = entry_index;
    a.block_index = block_index;
    a.block_buffer = block_buffer;
    a.block_length = block_length;
    a.table_buffer = table_buffer;
    a.table_length = table_length;
    errno = 0;
    return ioctl(fd, 0xC0284406, &a);
}

// Logical package IDs recovered from updater/Safe Mode analysis and confirmed
// payloads. IMPORTANT: for TABLE segments (flags & 1), the ID field is the
// TARGET SEGMENT INDEX, not a logical package ID.
static const char* package_name(uint32_t id) {
    switch (id) {
        case 0x001: return "eula";
        case 0x002: return "updatemode";
        case 0x003: return "emc_salina_a";
        case 0x004: return "mbr";
        case 0x005: return "kernel";
        case 0x00A: return "cp";
        case 0x00B: return "titania";
        case 0x00C: return "version_name";
        case 0x00D: return "emc_salina_b";
        case 0x00E: return "eap_kbl";
        case 0x00F: return "bd_firm_info";
        case 0x010: return "emc_salina_c";
        case 0x011: return "floyd_salina_c";
        case 0x012: return "usb_pdc_salina_c";
        // 0x013 is handled by updater code; semantic name not confirmed yet.
        case 0x014: return "emc_salina_d";
        case 0x015: return "eap_kbl_2";
        case 0x016: return "font";

        case 0x100: return "ariel_sec_ldr_a";
        case 0x101: return "oberon_sec_ldr_a";
        case 0x102: return "oberon_sec_ldr_b";
        case 0x103: return "oberon_sec_ldr_c";
        case 0x104: return "oberon_sec_ldr_d";
        case 0x105: return "oberon_sec_ldr_e";
        case 0x106: return "oberon_sec_ldr_f";
        // 0x107 is supported by updater code; semantic name not confirmed yet.

        case 0x201: return "wlanbt";
        case 0x203: return "system";
        case 0x204: return "system_ex";
        case 0x207: return "preinst";

        case 0x2F0: return "qa_test_1";
        case 0x2F1: return "qa_test_2";
        case 0x2F2: return "qa_test_3";
        default: return nullptr;
    }
}

static void segment_target_description(char* out, size_t cap, int index,
                                       const PupSegment* segs, int count) {
    if (!out || cap == 0 || !segs || index < 0 || index >= count) return;
    out[0] = 0;
    const PupSegment& s = segs[index];
    const uint32_t id = s.flags >> 20;

    if (s.flags & 1) {
        const uint32_t target_index = id;
        if (target_index < static_cast<uint32_t>(count)) {
            const uint32_t target_id = segs[target_index].flags >> 20;
            const char* name = package_name(target_id);
            if (name) {
                std::snprintf(out, cap, "TABLE->seg_%03u id_%03X %s",
                              target_index, target_id, name);
            } else {
                std::snprintf(out, cap, "TABLE->seg_%03u id_%03X",
                              target_index, target_id);
            }
        } else {
            std::snprintf(out, cap, "TABLE->seg_%03u", target_index);
        }
        return;
    }

    const char* name = package_name(id);
    if (name) std::snprintf(out, cap, "%s", name);
}

static int pup_type_from_name(const char* name) {
    if (!strcmp(name, "PS5UPDATE1.PUP") || !strcmp(name, "PROSPEROUPDATE1.PUP")) return 1;
    if (!strcmp(name, "PS5UPDATE2.PUP") || !strcmp(name, "PROSPEROUPDATE2.PUP")) return 0;
    return -1;
}

static int find_table_segment(int target_index, const PupSegment* segs, int count) {
    if (((target_index | 0x100) & 0xF00) == 0xF00) return -1;
    for (int i = 0; i < count; ++i) {
        if (segs[i].flags & 1) {
            uint32_t id = segs[i].flags >> 20;
            if (id == static_cast<uint32_t>(target_index)) return i;
        }
    }
    return -1;
}

static bool verify_signature_segments(int input_fd, uint64_t base, int devfd,
                                      const PupSegment* segs, int count) {
    for (int pass = 0; pass < 2; ++pass) {
        const uint32_t want = pass == 0 ? 0xE0000000u : 0xF0000000u;
        for (int i = 0; i < count; ++i) {
            if ((segs[i].flags & 0xF0000000u) != want) continue;
            const size_t len = static_cast<size_t>(segs[i].compressed_size);
            void* buf = alloc_aligned(len);
            if (!buf) return false;
            if (!pread_exact(input_fd, base + segs[i].offset, buf, len)) {
                logf("[!] Failed reading signature segment index=%d\n", i);
                free(buf);
                return false;
            }
            int r = ioctl_verify_segment(devfd, static_cast<uint16_t>(i), buf, len, pass == 0);
            int e = errno;
            logf("[*] verify segment index=%d kind=%s -> ret=%d errno=%d (%s)\n",
                 i, pass == 0 ? "additional-sign" : "watermark", r, e, strerror(e));
            free(buf);
            if (r < 0) return false;
        }
    }
    return true;
}

static void log_printable_blob(const uint8_t* data, size_t size);

static const char* known_segment_label(uint32_t id) {
    return package_name(id);
}

static const char* detect_blob_type(const uint8_t* data, size_t size) {
    if (!data || !size) return "empty";
    size_t p = 0;
    while (p < size && (data[p] == ' ' || data[p] == '\t' || data[p] == '\r' || data[p] == '\n')) ++p;
    if (size >= 11 && data[0] == 0xEB && data[2] == 0x90 && std::memcmp(data + 3, "EXFAT   ", 8) == 0)
        return "exfat";
    if (size >= 4 && data[0] == 0x7F && data[1] == 'E' && data[2] == 'L' && data[3] == 'F')
        return "elf";
    if (size >= 16 && std::memcmp(data, "SQLite format 3\0", 16) == 0)
        return "sqlite";
    if (size >= 4 && data[0] == 'P' && data[1] == 'K' && data[2] == 0x03 && data[3] == 0x04)
        return "zip";
    if (size >= 2 && data[0] == 0x1F && data[1] == 0x8B)
        return "gzip";
    if (size >= 8 && data[0] == 0x89 && data[1] == 'P' && data[2] == 'N' && data[3] == 'G')
        return "png";
    if (size >= 3 && data[0] == 0xFF && data[1] == 0xD8 && data[2] == 0xFF)
        return "jpeg";
    if (p + 5 <= size && std::memcmp(data + p, "<?xml", 5) == 0)
        return "xml";
    if (p < size && data[p] == '<')
        return "xml-like";
    if (p < size && (data[p] == '{' || data[p] == '['))
        return "json-like";
    if (size >= 2) {
        const uint16_t z = static_cast<uint16_t>((data[0] << 8) | data[1]);
        if ((data[0] & 0x0F) == 8 && (data[0] >> 4) <= 7 && (z % 31) == 0 && !(data[1] & 0x20))
            return "zlib";
    }
    return "binary";
}

static void make_segment_output_path(char* out, size_t cap, const char* entry_name,
                                     int index, const PupSegment* segs, int count,
                                     const char* suffix) {
    if (!out || cap == 0 || !entry_name || !segs || index < 0 || index >= count) return;
    out[0] = 0;
    const PupSegment& s = segs[index];
    const uint32_t id = s.flags >> 20;

    // TABLE: the segment ID is the target segment index. Resolve that target
    // and include both its index and logical package ID in the filename.
    if (s.flags & 1) {
        const uint32_t target_index = id;
        if (target_index < static_cast<uint32_t>(count)) {
            const uint32_t target_id = segs[target_index].flags >> 20;
            const char* target_label = package_name(target_id);
            if (target_label) {
                std::snprintf(out, cap,
                              "%s/%s.seg_%03d.table_for_seg_%03u.id_%03X.%s.%s",
                              OUTPUT_DIR, entry_name, index, target_index,
                              target_id, target_label, suffix);
            } else {
                std::snprintf(out, cap,
                              "%s/%s.seg_%03d.table_for_seg_%03u.id_%03X.%s",
                              OUTPUT_DIR, entry_name, index, target_index,
                              target_id, suffix);
            }
        } else {
            std::snprintf(out, cap, "%s/%s.seg_%03d.table_for_seg_%03u.%s",
                          OUTPUT_DIR, entry_name, index, target_index, suffix);
        }
        return;
    }

    // Familiar names for confirmed large payloads.
    if (std::strcmp(suffix, "dec.bin") == 0) {
        if (id == 0x201) { std::snprintf(out, cap, "%s/wlanbt.bin", OUTPUT_DIR); return; }
        if (id == 0x203) { std::snprintf(out, cap, "%s/ssd0.system.img", OUTPUT_DIR); return; }
        if (id == 0x204) { std::snprintf(out, cap, "%s/ssd0.system_ex.img", OUTPUT_DIR); return; }
        if (id == 0x207) { std::snprintf(out, cap, "%s/ssd0.preinst.img", OUTPUT_DIR); return; }
        if (id == 0x00C) { std::snprintf(out, cap, "%s/%s.seg_%03d.id_00C.version_name.xml",
                                         OUTPUT_DIR, entry_name, index); return; }
    }

    const char* label = known_segment_label(id);
    if (label) {
        std::snprintf(out, cap, "%s/%s.seg_%03d.id_%03X.%s.%s",
                      OUTPUT_DIR, entry_name, index, id, label, suffix);
    } else {
        std::snprintf(out, cap, "%s/%s.seg_%03d.id_%03X.%s",
                      OUTPUT_DIR, entry_name, index, id, suffix);
    }
}

static bool read_file_prefix(const char* path, uint8_t* buf, size_t cap, size_t* got) {
    if (!buf || !got || cap == 0) return false;
    *got = 0;
    int fd = open(path, O_RDONLY, 0);
    if (fd < 0) return false;
    ssize_t r = read(fd, buf, cap);
    close(fd);
    if (r < 0) return false;
    *got = static_cast<size_t>(r);
    return true;
}

static void manifest_row(const char* entry_name, int index, const PupSegment& s,
                         const char* category, const char* status,
                         const char* detected_type, const char* path) {
    if (!g_manifest) return;
    std::fprintf(g_manifest,
                 "%s\t%d\t%03X\t%08X\t%08X\t%016llX\t%016llX\t%016llX\t%s\t%s\t%s\t%s\n",
                 entry_name, index, s.flags >> 20, s.flags, s.flags2,
                 static_cast<unsigned long long>(s.offset),
                 static_cast<unsigned long long>(s.compressed_size),
                 static_cast<unsigned long long>(s.uncompressed_size),
                 category ? category : "", status ? status : "",
                 detected_type ? detected_type : "", path ? path : "");
    std::fflush(g_manifest);
}

static bool dump_raw_segment(int input_fd, uint64_t base, const char* entry_name,
                             int index, const PupSegment* segs, int count,
                             const char* category) {
    if (!segs || index < 0 || index >= count) return false;
    const PupSegment& s = segs[index];
    if (s.offset < 0 || s.compressed_size == 0 ||
        s.compressed_size > static_cast<uint64_t>(std::numeric_limits<size_t>::max()))
        return false;
    const size_t len = static_cast<size_t>(s.compressed_size);
    uint8_t* buf = static_cast<uint8_t*>(malloc(len));
    if (!buf) return false;
    const bool ok = pread_exact(input_fd, base + static_cast<uint64_t>(s.offset), buf, len);
    char path[320]{};
    make_segment_output_path(path, sizeof(path), entry_name, index, segs, count, "raw.bin");
    if (!make_unique_path(path, sizeof(path))) { free(buf); return false; }
    bool wrote = false;
    if (ok) {
        int fd = open(path, O_WRONLY | O_CREAT | O_EXCL, 0666);
        if (fd >= 0) {
            size_t done = 0;
            while (done < len) {
                ssize_t w = write(fd, buf + done, len - done);
                if (w <= 0) break;
                done += static_cast<size_t>(w);
            }
            wrote = done == len;
            close(fd);
        }
    }
    const char* type = ok ? detect_blob_type(buf, std::min<size_t>(len, 4096)) : "unreadable";
    manifest_row(entry_name, index, s, category, wrote ? "RAW_SAVED" : "FAILED", type, wrote ? path : "");
    logf("[segment %d id=0x%03X] %s raw %s%s%s\n", index, s.flags >> 20,
         category, wrote ? "saved=" : "FAILED", wrote ? path : "", wrote ? "" : "");
    free(buf);
    return wrote;
}

static bool dump_whole_segment(int input_fd, uint64_t base, int devfd,
                               const char* entry_name, int index,
                               const PupSegment* segs, int count) {
    if (!segs || index < 0 || index >= count) return false;
    const PupSegment& s = segs[index];
    if (s.offset < 0 || s.compressed_size == 0 || s.uncompressed_size == 0 ||
        s.compressed_size > static_cast<uint64_t>(std::numeric_limits<size_t>::max()) ||
        s.uncompressed_size > static_cast<uint64_t>(std::numeric_limits<size_t>::max()))
        return false;

    const bool compressed = (s.flags & 8) != 0;
    const size_t stored_total = static_cast<size_t>(s.compressed_size);
    size_t decrypt_len = stored_total;
    size_t payload_len = stored_total;
    if (compressed) {
        const size_t padding = stored_total & 0x0F;
        decrypt_len = stored_total & ~static_cast<size_t>(0x0F);
        if (decrypt_len == 0) decrypt_len = stored_total;
        payload_len = decrypt_len;
        if (padding <= payload_len) payload_len -= padding;
    }
    if (decrypt_len == 0) return false;

    uint8_t* buf = static_cast<uint8_t*>(alloc_aligned(decrypt_len));
    if (!buf || !pread_exact(input_fd, base + static_cast<uint64_t>(s.offset), buf, decrypt_len)) {
        free(buf);
        return false;
    }
    const int ret = ioctl_decrypt_segment(devfd, static_cast<uint16_t>(index), buf, decrypt_len);
    if (ret < 0) {
        logf("[segment %d id=0x%03X] WHOLE decrypt failed ret=%d errno=%d (%s)\n",
             index, s.flags >> 20, ret, errno, strerror(errno));
        free(buf);
        return false;
    }

    uint8_t* final_data = buf;
    size_t final_size = payload_len;
    uint8_t* inflated = nullptr;
    const char* mode = "RAW";
    if (compressed) {
        inflated = static_cast<uint8_t*>(malloc(static_cast<size_t>(s.uncompressed_size)));
        size_t produced = 0;
        if (inflated && inflate_block(buf, payload_len, inflated,
                                      static_cast<size_t>(s.uncompressed_size), &produced) == INFLATE_OK &&
            produced == static_cast<size_t>(s.uncompressed_size)) {
            final_data = inflated;
            final_size = produced;
            mode = "ZLIB";
        } else if (payload_len == static_cast<size_t>(s.uncompressed_size)) {
            final_data = buf;
            final_size = payload_len;
            mode = "RAW";
        } else {
            logf("[segment %d id=0x%03X] WHOLE decompression failed csize=0x%zx usize=0x%llX\n",
                 index, s.flags >> 20, payload_len,
                 static_cast<unsigned long long>(s.uncompressed_size));
            free(inflated);
            free(buf);
            return false;
        }
    } else {
        if (final_size > static_cast<size_t>(s.uncompressed_size))
            final_size = static_cast<size_t>(s.uncompressed_size);
    }

    char path[320]{};
    make_segment_output_path(path, sizeof(path), entry_name, index, segs, count, "dec.bin");
    if (!make_unique_path(path, sizeof(path))) { free(inflated); free(buf); return false; }
    int fd = open(path, O_WRONLY | O_CREAT | O_EXCL, 0666);
    bool wrote = false;
    if (fd >= 0) {
        size_t done = 0;
        while (done < final_size) {
            ssize_t w = write(fd, final_data + done, final_size - done);
            if (w <= 0) break;
            done += static_cast<size_t>(w);
        }
        wrote = done == final_size;
        close(fd);
    }
    const char* type = detect_blob_type(final_data, std::min<size_t>(final_size, 4096));
    const char* category = (s.flags & 1) ? "TABLE" : "WHOLE";
    manifest_row(entry_name, index, s, category, wrote ? mode : "FAILED", type, wrote ? path : "");
    logf("[segment %d id=0x%03X] %s mode=%s size=0x%zx type=%s %s%s\n",
         index, s.flags >> 20, category, mode, final_size, type,
         wrote ? "saved=" : "FAILED ", wrote ? path : "");
    if (final_size <= 1024) log_printable_blob(final_data, final_size);
    free(inflated);
    free(buf);
    return wrote;
}

static bool decode_block_segment_memory(int input_fd, uint64_t base, int devfd,
                                        int index, const PupSegment* segs, int count,
                                        uint8_t** out_data, size_t* out_size) {
    if (!out_data || !out_size) return false;
    *out_data = nullptr;
    *out_size = 0;

    const PupSegment& s = segs[index];
    if (!(s.flags & 0x800) || s.uncompressed_size == 0 ||
        s.uncompressed_size > 4 * 1024 * 1024ULL ||
        s.uncompressed_size > static_cast<uint64_t>(std::numeric_limits<size_t>::max()))
        return false;

    const int table_index = find_table_segment(index, segs, count);
    if (table_index < 0) return false;
    const PupSegment& ts = segs[table_index];
    if (ts.offset < 0 || ts.compressed_size == 0 ||
        ts.compressed_size > static_cast<uint64_t>(std::numeric_limits<size_t>::max()))
        return false;

    const size_t table_len = static_cast<size_t>(ts.compressed_size);
    uint8_t* table = static_cast<uint8_t*>(alloc_aligned(table_len));
    if (!table || !pread_exact(input_fd, base + ts.offset, table, table_len)) {
        free(table);
        return false;
    }
    if (ioctl_decrypt_segment(devfd, static_cast<uint16_t>(table_index), table, table_len) < 0) {
        free(table);
        return false;
    }

    const uint64_t block_size64 = 1ULL << (((s.flags & 0xF000u) >> 12) + 12);
    const uint64_t block_count = (s.uncompressed_size + block_size64 - 1) / block_size64;
    if (!block_count || block_size64 > static_cast<uint64_t>(std::numeric_limits<size_t>::max()) ||
        block_count > std::numeric_limits<size_t>::max() / 32 ||
        block_count * 32 > table_len ||
        block_count > (table_len - static_cast<size_t>(block_count * 32)) / sizeof(PupBlockInfo)) {
        free(table);
        return false;
    }

    const size_t block_size = static_cast<size_t>(block_size64);
    const PupBlockInfo* blocks = reinterpret_cast<const PupBlockInfo*>(table + block_count * 32);
    const size_t total_size = static_cast<size_t>(s.uncompressed_size);
    uint8_t* result = static_cast<uint8_t*>(malloc(total_size));
    if (!result) { free(table); return false; }

    bool ok = true;
    for (uint64_t bi = 0; bi < block_count; ++bi) {
        const size_t output_off = static_cast<size_t>(bi * block_size64);
        const size_t expected = static_cast<size_t>(std::min<uint64_t>(block_size64,
                                                s.uncompressed_size - bi * block_size64));
        BlockReadPlan plan{};
        if (s.offset < 0 || !block_read_plan(blocks[bi], s.flags2, s.compressed_size,
                                             block_size, expected, bi + 1 == block_count, &plan)) {
            ok = false; break;
        }

        uint8_t* enc = static_cast<uint8_t*>(alloc_aligned(plan.read_size));
        if (!enc || !pread_exact(input_fd, base + s.offset + blocks[bi].offset, enc, plan.read_size)) {
            free(enc); ok = false; break;
        }
        if (ioctl_decrypt_block(devfd, static_cast<uint16_t>(index), static_cast<uint16_t>(bi),
                                enc, plan.read_size, table, table_len) < 0) {
            free(enc); ok = false; break;
        }

        if (plan.compressed) {
            size_t produced = 0;
            if (inflate_block(enc, plan.read_size, result + output_off, expected, &produced) != INFLATE_OK ||
                produced != expected) {
                free(enc); ok = false; break;
            }
        } else {
            if (plan.read_size != expected) { free(enc); ok = false; break; }
            std::memcpy(result + output_off, enc, expected);
        }
        free(enc);
    }

    free(table);
    if (!ok) { free(result); return false; }
    *out_data = result;
    *out_size = total_size;
    return true;
}

static bool extract_xml_tag_value(const uint8_t* data, size_t size,
                                  const char* tag, char* output, size_t output_cap) {
    if (!data || !tag || !output || output_cap < 2) return false;
    char open_tag[96]{};
    char close_tag[96]{};
    const int on = std::snprintf(open_tag, sizeof(open_tag), "<%s>", tag);
    const int cn = std::snprintf(close_tag, sizeof(close_tag), "</%s>", tag);
    if (on <= 0 || cn <= 0 || static_cast<size_t>(on) >= sizeof(open_tag) ||
        static_cast<size_t>(cn) >= sizeof(close_tag)) return false;

    const size_t open_len = static_cast<size_t>(on);
    const size_t close_len = static_cast<size_t>(cn);
    for (size_t i = 0; i + open_len <= size; ++i) {
        if (std::memcmp(data + i, open_tag, open_len) != 0) continue;
        const size_t value_start = i + open_len;
        for (size_t p = value_start; p + close_len <= size; ++p) {
            if (std::memcmp(data + p, close_tag, close_len) != 0) continue;
            const size_t value_len = p - value_start;
            if (!value_len || value_len + 1 > output_cap) return false;
            std::memcpy(output, data + value_start, value_len);
            output[value_len] = 0;
            return true;
        }
        return false;
    }
    return false;
}

static bool extract_ascii_key_value(const uint8_t* data, size_t size,
                                    const char* key, char* output, size_t output_cap) {
    if (!data || !key || !output || output_cap < 2) return false;
    const size_t key_len = std::strlen(key);
    if (!key_len || size < key_len) return false;

    for (size_t i = 0; i + key_len <= size; ++i) {
        if (std::memcmp(data + i, key, key_len) != 0) continue;
        size_t p = i + key_len;
        while (p < size && (data[p] == '"' || data[p] == '\'' || data[p] == ' ' ||
                            data[p] == '\t' || data[p] == ':' || data[p] == '=')) ++p;
        size_t n = 0;
        while (p < size && n + 1 < output_cap) {
            const unsigned char c = data[p];
            if (c == 0 || c == '"' || c == '\'' || c == ',' || c == '}' || c == ']' ||
                c == '\r' || c == '\n' || c == ' ' || c == '\t') break;
            if (c < 0x20 || c > 0x7e) break;
            output[n++] = static_cast<char>(c);
            ++p;
        }
        output[n] = 0;
        if (n) return true;
    }
    return false;
}

static void log_printable_blob(const uint8_t* data, size_t size) {
    logf("    printable: ");
    for (size_t i = 0; i < size; ++i) {
        const unsigned char c = data[i];
        if (c >= 0x20 && c <= 0x7e) logf("%c", c);
        else if (c == '\r' || c == '\n' || c == '\t') logf(" ");
        else logf(".");
    }
    logf("\n");
}

static void probe_pup_version_metadata(int input_fd, uint64_t base, int devfd,
                                       const char* entry_name,
                                       const PupSegment* segs, int count) {
    // Safe Mode's getPupPrefixVersion reads updater object ID 0x0C (VER_NAME).
    // The inner PUP also contains a small segment whose logical ID is 0x00C.
    // Decode it read-only and look for the same metadata keys.  If this mapping
    // differs on another firmware, the raw decoded blob is still saved for study.
    for (int i = 0; i < count; ++i) {
        if ((segs[i].flags >> 20) != 0x00Cu) continue;
        if (!(segs[i].flags & 0x800)) continue;

        uint8_t* data = nullptr;
        size_t size = 0;
        if (!decode_block_segment_memory(input_fd, base, devfd, i, segs, count, &data, &size)) {
            logf("[PUP version] entry=%s segment=0x00C index=%d decode failed\n", entry_name, i);
            continue;
        }

        char path[256]{};
        std::snprintf(path, sizeof(path), "%s/%s.segment_00C.dec.bin", OUTPUT_DIR, entry_name);
        if (!make_unique_path(path, sizeof(path))) {
            logf("[PUP version] failed to choose unique metadata path\n");
            free(data);
            continue;
        }
        int fd = open(path, O_WRONLY | O_CREAT | O_EXCL, 0666);
        if (fd >= 0) {
            size_t done = 0;
            while (done < size) {
                ssize_t w = write(fd, data + done, size - done);
                if (w <= 0) break;
                done += static_cast<size_t>(w);
            }
            close(fd);
        }

        logf("[PUP version] entry=%s segment=0x00C index=%d decoded_size=0x%zx saved=%s\n",
             entry_name, i, size, path);
        if (size <= 512) log_printable_blob(data, size);

        char version[64]{};
        if (extract_xml_tag_value(data, size, "prefix_version", version, sizeof(version))) {
            logf("[*] PUP prefix_version: %s (prefix only, not full system software version)\n", version);
        } else if (extract_ascii_key_value(data, size, "prefix_version", version, sizeof(version))) {
            logf("[*] PUP prefix_version candidate: %s\n", version);
        } else {
            logf("[PUP version] prefix_version key not found in decoded 0x00C blob\n");
        }
        free(data);
    }
}

#ifndef HOST_TEST
static void format_kernel_fw(uint32_t fw, char out[16]) {
    // PS5 SDK values such as 0x12400009 conventionally correspond to 12.40.x.
    std::snprintf(out, 16, "%02X.%02X", (fw >> 24) & 0xffu, (fw >> 16) & 0xffu);
}
#endif

static bool dump_block_segment(int input_fd, uint64_t base, int devfd,
                               const char* entry_name, int index,
                               const PupSegment* segs, int count) {
    const PupSegment& s = segs[index];
    const uint32_t id = s.flags >> 20;
    if (!(s.flags & 0x800)) return false;

    const int table_index = find_table_segment(index, segs, count);
    if (table_index < 0) {
        logf("[segment %d id=0x%03X] BLOCK table not found\n", index, id);
        manifest_row(entry_name, index, s, "BLOCK", "NO_TABLE", "", "");
        return false;
    }
    const PupSegment& ts = segs[table_index];
    if (ts.offset < 0 || ts.compressed_size == 0 ||
        ts.compressed_size > static_cast<uint64_t>(std::numeric_limits<size_t>::max())) {
        manifest_row(entry_name, index, s, "BLOCK", "BAD_TABLE", "", "");
        return false;
    }

    const size_t table_len = static_cast<size_t>(ts.compressed_size);
    uint8_t* table = static_cast<uint8_t*>(alloc_aligned(table_len));
    if (!table || !pread_exact(input_fd, base + static_cast<uint64_t>(ts.offset), table, table_len)) {
        free(table);
        manifest_row(entry_name, index, s, "BLOCK", "TABLE_READ_FAIL", "", "");
        return false;
    }
    int ret = ioctl_decrypt_segment(devfd, static_cast<uint16_t>(table_index), table, table_len);
    if (ret < 0) {
        logf("[segment %d id=0x%03X] BLOCK table decrypt failed ret=%d errno=%d (%s)\n",
             index, id, ret, errno, strerror(errno));
        free(table);
        manifest_row(entry_name, index, s, "BLOCK", "TABLE_DECRYPT_FAIL", "", "");
        return false;
    }

    const uint64_t block_size64 = 1ULL << (((s.flags & 0xF000u) >> 12) + 12);
    if (!block_size64 || block_size64 > static_cast<uint64_t>(std::numeric_limits<size_t>::max())) {
        free(table);
        return false;
    }
    const size_t block_size = static_cast<size_t>(block_size64);
    const uint64_t block_count = (s.uncompressed_size + block_size64 - 1) / block_size64;
    if (!block_count || block_count > static_cast<uint64_t>(std::numeric_limits<uint16_t>::max()) + 1) {
        free(table);
        return false;
    }

    const bool compressed = (s.flags & 8) != 0;
    const PupBlockInfo* blocks = nullptr;
    bool explicit_offsets = false;
    if (compressed) {
        if (block_count > std::numeric_limits<size_t>::max() / 32 ||
            block_count * 32 > table_len ||
            block_count > (table_len - static_cast<size_t>(block_count * 32)) / sizeof(PupBlockInfo)) {
            logf("[segment %d id=0x%03X] BLOCK invalid compressed block table count=%llu table=0x%zx\n",
                 index, id, static_cast<unsigned long long>(block_count), table_len);
            free(table);
            manifest_row(entry_name, index, s, "BLOCK", "BAD_BLOCK_TABLE", "", "");
            return false;
        }
        blocks = reinterpret_cast<const PupBlockInfo*>(table + block_count * 32);
        explicit_offsets = blocks[0].offset != 0;
    }

    char final_path[320]{};
    char partial_path[336]{};
    make_segment_output_path(final_path, sizeof(final_path), entry_name, index, segs, count, "dec.bin");
    if (!make_unique_path(final_path, sizeof(final_path), true)) {
        free(table);
        return false;
    }
    std::snprintf(partial_path, sizeof(partial_path), "%s.partial", final_path);
    int output_fd = create_output_file(partial_path, s.uncompressed_size);
    if (output_fd < 0) { free(table); return false; }

    logf("[segment %d id=0x%03X] BLOCK table=%d block_size=0x%zx blocks=%llu compressed=%s output=%s\n",
         index, id, table_index, block_size, static_cast<unsigned long long>(block_count),
         compressed ? "yes" : "no", partial_path);

    bool ok = true;
    uint64_t sequential_input = 0;
    uint64_t remaining_input = s.compressed_size;
    for (uint64_t bi = 0; bi < block_count; ++bi) {
        const uint64_t output_off = bi * block_size64;
        const size_t expected = static_cast<size_t>(std::min<uint64_t>(block_size64,
                                              s.uncompressed_size - output_off));
        size_t read_size = 0;
        uint64_t input_rel = sequential_input;
        bool block_compressed = false;

        if (compressed) {
            BlockReadPlan plan{};
            if (!block_read_plan(blocks[bi], s.flags2, s.compressed_size,
                                 block_size, expected, bi + 1 == block_count, &plan)) {
                ok = false; break;
            }
            read_size = plan.read_size;
            block_compressed = plan.compressed;
            if (explicit_offsets) input_rel = blocks[bi].offset;
        } else {
            read_size = static_cast<size_t>(std::min<uint64_t>(remaining_input, block_size64));
            block_compressed = false;
        }
        if (!read_size || input_rel > s.compressed_size || read_size > s.compressed_size - input_rel) {
            ok = false; break;
        }

        uint8_t* enc = static_cast<uint8_t*>(alloc_aligned(read_size));
        uint8_t* out = static_cast<uint8_t*>(malloc(expected));
        if (!enc || !out || !pread_exact(input_fd, base + static_cast<uint64_t>(s.offset) + input_rel,
                                         enc, read_size)) {
            free(enc); free(out); ok = false; break;
        }
        ret = ioctl_decrypt_block(devfd, static_cast<uint16_t>(index), static_cast<uint16_t>(bi),
                                  enc, read_size, table, table_len);
        if (ret < 0) {
            logf("[segment %d id=0x%03X] block=%llu decrypt failed ret=%d errno=%d (%s)\n",
                 index, id, static_cast<unsigned long long>(bi), ret, errno, strerror(errno));
            free(enc); free(out); ok = false; break;
        }

        size_t produced = 0;
        if (block_compressed) {
            if (inflate_block(enc, read_size, out, expected, &produced) != INFLATE_OK || produced != expected) {
                logf("[segment %d id=0x%03X] block=%llu inflate failed read=0x%zx expected=0x%zx\n",
                     index, id, static_cast<unsigned long long>(bi), read_size, expected);
                free(enc); free(out); ok = false; break;
            }
        } else {
            if (read_size != expected) {
                logf("[segment %d id=0x%03X] block=%llu RAW size mismatch read=0x%zx expected=0x%zx\n",
                     index, id, static_cast<unsigned long long>(bi), read_size, expected);
                free(enc); free(out); ok = false; break;
            }
            std::memcpy(out, enc, expected);
            produced = expected;
        }
        if (!write_exact_at(output_fd, output_off, out, produced)) {
            free(enc); free(out); ok = false; break;
        }
        free(enc);
        free(out);

        if (!explicit_offsets) sequential_input += read_size;
        if (!compressed) remaining_input -= read_size;
        if (bi < 4 || bi + 1 == block_count || ((bi + 1) % 64) == 0) {
            logf("    block %llu/%llu mode=%s read=0x%zx out=0x%zx progress=%llu%%\n",
                 static_cast<unsigned long long>(bi + 1),
                 static_cast<unsigned long long>(block_count),
                 block_compressed ? "ZLIB" : "RAW", read_size, produced,
                 static_cast<unsigned long long>((bi + 1) * 100 / block_count));
        }
    }

    close(output_fd);
    free(table);
    if (!ok) {
        logf("[segment %d id=0x%03X] BLOCK FAILED; partial=%s\n", index, id, partial_path);
        manifest_row(entry_name, index, s, "BLOCK", "FAILED", "", partial_path);
        return false;
    }
    if (rename(partial_path, final_path) != 0) {
        manifest_row(entry_name, index, s, "BLOCK", "RENAME_FAIL", "", partial_path);
        return false;
    }

    uint8_t prefix[4096]{};
    size_t got = 0;
    const char* type = "binary";
    if (read_file_prefix(final_path, prefix, sizeof(prefix), &got)) type = detect_blob_type(prefix, got);
    manifest_row(entry_name, index, s, "BLOCK", "DECODED", type, final_path);
    logf("[segment %d id=0x%03X] BLOCK COMPLETE size=0x%llX type=%s saved=%s\n",
         index, id, static_cast<unsigned long long>(s.uncompressed_size), type, final_path);
    return true;
}

#if 0  // Superseded first-block probe retained temporarily for reference.
static void probe_block_segment(int input_fd, uint64_t base, int devfd,
                                const char* entry_name, int index,
                                const PupSegment* segs, int count) {
    const PupSegment& s = segs[index];
    const uint32_t id = s.flags >> 20;
    const int table_index = find_table_segment(index, segs, count);
    if (table_index < 0) {
        logf("[!] target 0x%03X: block mode but table segment was not found\n", id);
        return;
    }

    const PupSegment& ts = segs[table_index];
    size_t table_len = static_cast<size_t>(ts.compressed_size);
    uint8_t* table = static_cast<uint8_t*>(alloc_aligned(table_len));
    if (!table) { logf("[!] table allocation failed\n"); return; }
    if (!pread_exact(input_fd, base + ts.offset, table, table_len)) {
        logf("[!] target 0x%03X: failed reading table index=%d\n", id, table_index);
        free(table); return;
    }

    int tr = ioctl_decrypt_segment(devfd, static_cast<uint16_t>(table_index), table, table_len);
    int te = errno;
    logf("[*] target 0x%03X: decrypt table index=%d -> ret=%d errno=%d (%s)\n",
         id, table_index, tr, te, strerror(te));
    if (tr < 0) { free(table); return; }

    const bool compressed = (s.flags & 8) != 0;
    const size_t block_size = static_cast<size_t>(1ULL << (((s.flags & 0xF000) >> 12) + 12));
    const uint64_t block_count = (block_size + s.uncompressed_size - 1) / block_size;
    if (block_count == 0) { free(table); return; }

    size_t read_size = block_size;
    uint64_t block_off = 0;
    if (compressed) {
        const size_t info_off = static_cast<size_t>(32 * block_count);
        if (info_off + sizeof(PupBlockInfo) > table_len) {
            logf("[!] target 0x%03X: table too small for block info\n", id);
            free(table); return;
        }
        const PupBlockInfo* bi = reinterpret_cast<const PupBlockInfo*>(table + info_off);
        const uint32_t mask = (s.flags2 & 1) ? 0x1ff : 0xf;
        const uint32_t unpadded = (bi[0].size & ~mask) - (bi[0].size & mask);
        const size_t tail_size0 = (s.uncompressed_size % block_size) ?
                                  static_cast<size_t>(s.uncompressed_size % block_size) : block_size;
        read_size = block_size;
        if (unpadded != block_size) {
            read_size = bi[0].size;
            const bool is_last = (block_count == 1);
            if (!is_last || tail_size0 != bi[0].size)
                read_size &= ~static_cast<size_t>(mask);
        }
        if (read_size == 0) read_size = bi[0].size;
        block_off = bi[0].offset;
    } else {
        read_size = static_cast<size_t>(std::min<uint64_t>(s.compressed_size, block_size));
    }

    if (read_size == 0 || read_size > block_size) {
        logf("[!] target 0x%03X: suspicious first block size=0x%zx block_size=0x%zx\n", id, read_size, block_size);
        free(table); return;
    }

    uint8_t* block = static_cast<uint8_t*>(alloc_aligned(block_size));
    uint8_t* before = static_cast<uint8_t*>(malloc(read_size));
    if (!block || !before) { free(table); free(block); free(before); return; }

    const uint64_t file_off = base + s.offset + block_off;
    if (!pread_exact(input_fd, file_off, block, read_size)) {
        logf("[!] target 0x%03X: failed reading first block at 0x%llX\n", id, (unsigned long long)file_off);
        free(table); free(block); free(before); return;
    }
    memcpy(before, block, read_size);

    logf("[*] target 0x%03X (%s): block mode, table=%d, block_size=0x%zx, first_read=0x%zx\n",
         id, package_name(id), table_index, block_size, read_size);
    hexdump_prefix("    BEFORE", before, read_size);

    int r = ioctl_decrypt_block(devfd, static_cast<uint16_t>(index), 0,
                                block, read_size, table, table_len);
    int e = errno;
    const bool changed = memcmp(before, block, read_size) != 0;
    logf("[*] target 0x%03X: decrypt block0 -> ret=%d errno=%d (%s), changed=%s\n",
         id, r, e, strerror(e), changed ? "YES" : "NO");
    hexdump_prefix("    AFTER ", block, read_size);

    char path[256];
    make_path(path, sizeof(path), entry_name, id, "block0.before.bin");
    write_file(path, before, read_size);
    make_path(path, sizeof(path), entry_name, id, "block0.after.bin");
    write_file(path, block, read_size);

    free(table); free(block); free(before);
}

static void probe_normal_segment(int input_fd, uint64_t base, int devfd,
                                 const char* entry_name, int index,
                                 const PupSegment& s) {
    const uint32_t id = s.flags >> 20;
    const size_t len = static_cast<size_t>(s.compressed_size);
    if (len == 0 || len > MAX_NONBLOCK_PROBE) {
        logf("[!] target 0x%03X (%s): non-block segment is 0x%zx bytes; skipping to avoid huge allocation\n",
             id, package_name(id), len);
        return;
    }

    uint8_t* buf = static_cast<uint8_t*>(alloc_aligned(len));
    uint8_t* before = static_cast<uint8_t*>(malloc(len));
    if (!buf || !before) { free(buf); free(before); return; }
    if (!pread_exact(input_fd, base + s.offset, buf, len)) {
        logf("[!] target 0x%03X: failed reading segment\n", id);
        free(buf); free(before); return;
    }
    memcpy(before, buf, len);
    hexdump_prefix("    BEFORE", before, len);
    int r = ioctl_decrypt_segment(devfd, static_cast<uint16_t>(index), buf, len);
    int e = errno;
    bool changed = memcmp(before, buf, len) != 0;
    logf("[*] target 0x%03X (%s): decrypt segment -> ret=%d errno=%d (%s), changed=%s\n",
         id, package_name(id), r, e, strerror(e), changed ? "YES" : "NO");
    hexdump_prefix("    AFTER ", buf, len);

    char path[256];
    make_path(path, sizeof(path), entry_name, id, "before.bin");
    write_file(path, before, len);
    make_path(path, sizeof(path), entry_name, id, "after.bin");
    write_file(path, buf, len);
    free(buf); free(before);
}

#endif

static void process_pup_entry(int input_fd, const uint8_t* bls_data,
                              const BlsEntry& be, uint32_t entry_no) {
    char entry_name[33]{};
    memcpy(entry_name, be.name, 32);
    const uint64_t base = static_cast<uint64_t>(be.block_offset) * 512ULL;
    logf("\n========== ENTRY %u: %s base=0x%llX size_blocks=0x%X ==========\n",
         entry_no, entry_name, (unsigned long long)base, be.size);

    int type = pup_type_from_name(entry_name);
    if (type < 0) {
        logf("[!] Unknown PUP entry type/name; skipping entry.\n");
        return;
    }

    int devfd = open("/dev/pup_update0", O_RDWR, 0);
    if (devfd < 0) {
        logf("[!] open(/dev/pup_update0) failed: errno=%d (%s)\n", errno, strerror(errno));
        return;
    }

    int vr = ioctl_verify_bls(devfd, const_cast<uint8_t*>(bls_data), BLS_HEADER_READ);
    int ve = errno;
    logf("[*] verify BLS -> ret=%d errno=%d (%s)\n", vr, ve, strerror(ve));
    if (vr < 0) { close(devfd); return; }

    PupFileHeader fh{};
    if (!pread_exact(input_fd, base, &fh, sizeof(fh))) {
        logf("[!] Failed to read PUP file header\n"); close(devfd); return;
    }
    if (fh.magic != PUP_MAGIC) {
        logf("[!] Invalid PUP magic: 0x%08X\n", fh.magic); close(devfd); return;
    }

    const size_t header_size = static_cast<size_t>(fh.unknown_0C) + fh.unknown_0E;
    if (header_size < sizeof(PupHeader) || header_size > 16 * 1024 * 1024) {
        logf("[!] Suspicious header_size=0x%zx\n", header_size); close(devfd); return;
    }
    uint8_t* header_buf = static_cast<uint8_t*>(alloc_aligned(header_size));
    if (!header_buf || !pread_exact(input_fd, base, header_buf, header_size)) {
        logf("[!] Failed to read complete PUP header\n"); free(header_buf); close(devfd); return;
    }

    hexdump_prefix("[*] encrypted PUP header prefix", header_buf, header_size);
    int hr = ioctl_decrypt_header(devfd, header_buf, header_size, type);
    int he = errno;
    logf("[*] decrypt PUP header -> ret=%d errno=%d (%s)\n", hr, he, strerror(he));
    if (hr < 0) { free(header_buf); close(devfd); return; }
    hexdump_prefix("[*] decrypted PUP header prefix", header_buf, header_size);

    const PupHeader* ph = reinterpret_cast<const PupHeader*>(header_buf);
    const int count = ph->segment_count;
    const size_t needed = 0x20 + static_cast<size_t>(count) * sizeof(PupSegment);
    logf("[*] file_size=0x%llX segment_count=%d header_size=0x%zx\n",
         (unsigned long long)ph->file_size, count, header_size);
    if (count <= 0 || count > 4096 || needed > header_size) {
        logf("[!] Invalid segment table bounds: needed=0x%zx\n", needed);
        free(header_buf); close(devfd); return;
    }

    {
        char header_path[320]{};
        std::snprintf(header_path, sizeof(header_path), "%s/%s.header.dec.bin", OUTPUT_DIR, entry_name);
        if (!make_unique_path(header_path, sizeof(header_path))) {
            logf("[!] failed to choose unique header output path\n");
        }
        int hfd = open(header_path, O_WRONLY | O_CREAT | O_EXCL, 0666);
        if (hfd >= 0) {
            size_t done = 0;
            while (done < header_size) {
                ssize_t w = write(hfd, header_buf + done, header_size - done);
                if (w <= 0) break;
                done += static_cast<size_t>(w);
            }
            close(hfd);
            logf("[*] saved decrypted PUP header: %s\n", header_path);
        }
    }

    const PupSegment* segs = reinterpret_cast<const PupSegment*>(header_buf + 0x20);
    logf("\n[index] id    flags       flags2      offset             csize              usize              mode target\n");
    for (int i = 0; i < count; ++i) {
        const uint32_t id = segs[i].flags >> 20;
        char target_desc[128]{};
        segment_target_description(target_desc, sizeof(target_desc), i, segs, count);
        logf("[%4d] %03X  %08X  %08X  %016llX  %016llX  %016llX  %s %s\n",
             i, id, segs[i].flags, segs[i].flags2,
             (unsigned long long)segs[i].offset,
             (unsigned long long)segs[i].compressed_size,
             (unsigned long long)segs[i].uncompressed_size,
             (segs[i].flags & 0x800) ? "BLOCK" : "WHOLE",
             target_desc);
    }

    if (!verify_signature_segments(input_fd, base, devfd, segs, count)) {
        logf("[!] Signature/watermark verification did not complete successfully; continuing probe anyway.\n");
    }

    probe_pup_version_metadata(input_fd, base, devfd, entry_name, segs, count);

    // Universal extraction: every segment gets a deterministic index+ID filename.
    // Special signature/watermark segments are preserved RAW; normal segments are decrypted
    // and decompressed according to their WHOLE/BLOCK layout.
    logf("\n========== UNIVERSAL SEGMENT EXTRACTION: %s ==========\n", entry_name);
    for (int i = 0; i < count; ++i) {
        const PupSegment& s = segs[i];
        const uint32_t id = s.flags >> 20;
        const uint32_t special = s.flags & 0xF0000000u;
        if (special == 0xE0000000u) {
            dump_raw_segment(input_fd, base, entry_name, i, segs, count, "ADDITIONAL_SIGNATURE");
            continue;
        }
        if (special == 0xF0000000u) {
            dump_raw_segment(input_fd, base, entry_name, i, segs, count, "WATERMARK");
            continue;
        }
        if (s.flags & 0x800) {
            dump_block_segment(input_fd, base, devfd, entry_name, i, segs, count);
        } else {
            if (!dump_whole_segment(input_fd, base, devfd, entry_name, i, segs, count)) {
                logf("[segment %d id=0x%03X] WHOLE decode failed; preserving encrypted/raw bytes\n", i, id);
                dump_raw_segment(input_fd, base, entry_name, i, segs, count, (s.flags & 1) ? "TABLE_RAW_FALLBACK" : "WHOLE_RAW_FALLBACK");
            }
        }
    }

    free(header_buf);
    close(devfd);
}

static const char* find_input() {
    for (const char* p : INPUT_CANDIDATES) {
        int fd = open(p, O_RDONLY, 0);
        if (fd >= 0) { close(fd); return p; }
    }
    return nullptr;
}

int main() {
    mkdir(OUTPUT_DIR, 0777);

    char actual_log_path[256]{};
    std::snprintf(actual_log_path, sizeof(actual_log_path), "%s", LOG_PATH);
    if (make_unique_path(actual_log_path, sizeof(actual_log_path))) {
        int log_fd = open(actual_log_path, O_WRONLY | O_CREAT | O_EXCL, 0666);
        if (log_fd >= 0) {
            g_log = fdopen(log_fd, "w");
            if (!g_log) close(log_fd);
        }
    }

    char manifest_path[256]{};
    std::snprintf(manifest_path, sizeof(manifest_path), "%s/segments_manifest.tsv", OUTPUT_DIR);
    if (make_unique_path(manifest_path, sizeof(manifest_path))) {
        int manifest_fd = open(manifest_path, O_WRONLY | O_CREAT | O_EXCL, 0666);
        if (manifest_fd >= 0) {
            g_manifest = fdopen(manifest_fd, "w");
            if (!g_manifest) close(manifest_fd);
        }
    }
    if (g_manifest) {
        std::fprintf(g_manifest, "entry\tindex\tid\tflags\tflags2\toffset\tcsize\tusize\tcategory\tstatus\ttype\tpath\n");
        std::fflush(g_manifest);
    }

    logf("PS5 PUP universal segment dumper V5\n");
    logf("No-overwrite output naming enabled (_1, _2, ...).\n");
    logf("Log: %s\n", actual_log_path);
    logf("Extracts named and unnamed PUP segments; read-only toward internal storage.\n");
    logf("Output is USB only. Manifest: %s\n\n", manifest_path);

#ifndef HOST_TEST
    pid_t pid = getpid();
    uint64_t auth_before = kernel_get_ucred_authid(pid);
    uint32_t fw = kernel_get_fw_version();
    int ar = kernel_set_ucred_authid(pid, 0x4801000000000013ULL);
    int rr = kernel_set_proc_rootdir(pid, kernel_get_root_vnode());
    uint64_t auth_after = kernel_get_ucred_authid(pid);
    char fw_text[16]{};
    format_kernel_fw(fw, fw_text);
    logf("[*] Console firmware=%s raw=0x%08X pid=%d\n", fw_text, fw, pid);
    logf("[*] privilege setup: authid 0x%016llX -> 0x%016llX, authid_ret=%d rootdir_ret=%d\n",
         (unsigned long long)auth_before, (unsigned long long)auth_after, ar, rr);
#else
    logf("[*] HOST_TEST build: PS5 privilege calls are stubbed\n");
#endif

    const char* input = find_input();
    if (!input) {
        logf("[!] Input PUP not found. Tried:\n");
        for (const char* p : INPUT_CANDIDATES) logf("    %s\n", p);
        if (g_manifest) fclose(g_manifest);
        if (g_log) fclose(g_log);
        return 1;
    }
    logf("[*] Input: %s\n", input);

    int fd = open(input, O_RDONLY, 0);
    if (fd < 0) {
        logf("[!] Failed to open input: %s\n", strerror(errno));
        if (g_manifest) fclose(g_manifest);
        if (g_log) fclose(g_log);
        return 1;
    }

    uint8_t* bls = static_cast<uint8_t*>(alloc_aligned(BLS_HEADER_READ));
    if (!bls || !pread_exact(fd, 0, bls, BLS_HEADER_READ)) {
        logf("[!] Failed to read first 0x400 bytes\n");
        free(bls); close(fd); if (g_manifest) fclose(g_manifest); if (g_log) fclose(g_log); return 1;
    }
    const BlsHeader* bh = reinterpret_cast<const BlsHeader*>(bls);
    if (bh->magic != BLS_MAGIC) {
        logf("[!] Expected BLS wrapper magic 0x%08X, got 0x%08X\n", BLS_MAGIC, bh->magic);
        logf("    This probe currently expects the outer PROSPERO/PS5 update container, not a raw inner PUP.\n");
        free(bls); close(fd); if (g_manifest) fclose(g_manifest); if (g_log) fclose(g_log); return 1;
    }
    logf("[*] BLS: version=%u flags=0x%X file_count=%u block_count=%u\n",
         bh->version, bh->flags, bh->file_count, bh->block_count);
    if (bh->file_count < 1 || bh->file_count > 10 ||
        sizeof(BlsHeader) + static_cast<size_t>(bh->file_count) * sizeof(BlsEntry) > BLS_HEADER_READ) {
        logf("[!] Invalid BLS entry count/table\n");
        free(bls); close(fd); if (g_manifest) fclose(g_manifest); if (g_log) fclose(g_log); return 1;
    }

    for (uint32_t i = 0; i < bh->file_count; ++i)
        process_pup_entry(fd, bls, bh->entry_list[i], i + 1);

    logf("\n[*] Dump run complete. Output directory: %s\n", OUTPUT_DIR);
    free(bls);
    close(fd);
    if (g_manifest) fclose(g_manifest);
    if (g_log) fclose(g_log);
    return 0;
}
