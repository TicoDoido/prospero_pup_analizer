PS5 PUP FULL ANALIZER  
===================================  

Purpose  
-------  
Non-destructive research payload that reconstructs all block-based PUP data  

It never opens /dev/ssd0, /dev/ssd0.system, or /dev/ssd0.system_ex and never  
formats, mounts, partitions, or writes internal storage.  All output is USB only.  

Expected input (first path tried)  
---------------------------------  
/mnt/usb0/PROSPERO/UPDATE/PROSPEROUPDATE.PUP  

Fallbacks:  
/mnt/usb0/PS5UPDATE.PUP  
/mnt/usb0/PROSPEROUPDATE.PUP  

Output  
------  
/mnt/usb0/pup_dump/pup_dump.log  
/mnt/usb0/pup_dump/example.bin  

The dumper pre-creates each output at its declared uncompressed size. On a  
block/decrypt/inflate/write error the in-progress file remains as *.partial.  

Processing  
----------  
For every block the payload reads the offset and aligned stored size from  
PupBlockInfo and calls DecryptPupSegmentBlock. It first tries zlib inflate; if  
that fails and the stored size equals the logical block size, it writes the  
decrypted bytes as a RAW fallback. The log records all table and block metadata,  
IOCTL/inflate returns, block mode, errno, logical output offsets, and progress.  

Build  
-----  
Use a current ps5-payload-dev/sdk installation:  

  export PS5_PAYLOAD_SDK=/opt/ps5-payload-sdk  
  make  

Produces:  
  pup-full-dump.elf  

Deploy example:  

  export PS5_HOST=<PS5 IP>  
  export PS5_PORT=9021  
  make test  

Notes  
-----  
- Requires an ELF loader environment where kernel_sys privilege helpers work.  
- The inflater is integrated, so no zlib SDK library is required.  
- It verifies the outer BLS context before probing an inner PUP entry.  
- It only reconstructs the expected block-based target segments. A target in  
  another mode is logged and skipped rather than being interpreted as a block table.  


After that, you can use ps5_texfat_explorer.py to extract the .IMG files,  
since they are simply partitions in exFAT format.  
Optional PS5 FTP round-trip for SELF .ebin/.bin/.elf/.sprx -> decrypted ELF using ftpsrv.  
