ifeq ($(origin CC),default)
CC       = gcc
endif
CFLAGS   ?= -O2 -march=native
CPPFLAGS ?= -DNDEBUG
LDLIBS   ?= -lmpfr -lgmp -lm

.PHONY: all noomp selftest bench clean

all: intmul_fastdft

intmul_fastdft: intmul_fastdft.c
	$(CC) $(CFLAGS) -fopenmp $(CPPFLAGS) intmul_fastdft.c -o intmul_fastdft $(LDLIBS)

noomp:
	$(CC) $(CFLAGS) -DINTMUL_NO_OPENMP $(CPPFLAGS) -Wno-unknown-pragmas intmul_fastdft.c -o intmul_fastdft $(LDLIBS)

selftest:
	./scripts/selftest.sh

bench:
	./scripts/bench.sh

clean:
	rm -f intmul_fastdft *.o bench/logs/*.tmp
