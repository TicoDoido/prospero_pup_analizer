PS5_HOST ?= ps5
PS5_PORT ?= 9021

ifndef PS5_PAYLOAD_SDK
$(error PS5_PAYLOAD_SDK is undefined; e.g. export PS5_PAYLOAD_SDK=/opt/ps5-payload-sdk)
endif

include $(PS5_PAYLOAD_SDK)/toolchain/prospero.mk

ELF := pup-full-dump.elf
CXXFLAGS := -std=c++11 -O1 -g -Wall -Wextra -I.
LDADD := -lkernel_sys

all: $(ELF)

$(ELF): pup-full-dump.cpp
	$(CXX) $(CXXFLAGS) -o $@ $< $(LDADD)

clean:
	rm -f $(ELF)

test: $(ELF)
	$(PS5_DEPLOY) -h $(PS5_HOST) -p $(PS5_PORT) $<
