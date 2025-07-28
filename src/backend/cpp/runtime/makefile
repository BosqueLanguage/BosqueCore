MAKE_PATH=$(realpath $(dir $(lastword $(MAKEFILE_LIST))))
GC_PATH=$(MAKE_PATH)/gc
BUILD_DIR=$(GC_PATH)/build/
SRC_DIR=$(GC_PATH)/src/
CPPEMIT_DIR=$(MAKE_PATH)/

RUNTIME_DIR=$(SRC_DIR)runtime/
SUPPORT_DIR=$(SRC_DIR)runtime/support/
MEMORY_DIR=$(SRC_DIR)runtime/memory/

OUT_EXE=$(MAKE_PATH)/output/
OUT_OBJ=$(MAKE_PATH)/output/obj/

TEST_DIR=$(MAKE_PATH)/../test/
MEMORY_TEST_DIR=$(MAKE_PATH)/../test/memory/

LANGUAGE_DIR=$(MAKE_PATH)/../src/language/

#dev is default, for another flavor : make BUILD=release or debug
BUILD := dev

CC=g++
CSTDFLAGS=-Wall -Wextra -Wno-unused-parameter -Wuninitialized -Werror -std=gnu++20 -fno-exceptions -fno-rtti -fno-strict-aliasing -fno-omit-frame-pointer -fno-stack-protector

CFLAGS_OPT.dev=-O0 -g -ggdb 
CFLAGS_OPT.release=-O2 -march=x86-64-v3
CFLAGS=${CFLAGS_OPT.${BUILD}} ${CSTDFLAGS}

SUPPORT_HEADERS=$(RUNTIME_DIR)common.h $(SUPPORT_DIR)xalloc.h $(SUPPORT_DIR)arraylist.h $(SUPPORT_DIR)pagetable.h $(SUPPORT_DIR)qsort.h 
SUPPORT_SOURCES=$(RUNTIME_DIR)common.cpp $(SUPPORT_DIR)xalloc.cpp
SUPPORT_OBJS=$(OUT_OBJ)common.o $(OUT_OBJ)xalloc.o

MEMORY_HEADERS=$(RUNTIME_DIR)common.h $(MEMORY_DIR)allocator.h $(MEMORY_DIR)threadinfo.h $(MEMORY_DIR)gc.h
MEMORY_SOURCES=$(MEMORY_DIR)allocator.cpp $(MEMORY_DIR)threadinfo.cpp $(MEMORY_DIR)gc.cpp
MEMORY_OBJS=$(OUT_OBJ)allocator.o $(OUT_OBJ)threadinfo.o $(OUT_OBJ)gc.o 

all: $(OUT_EXE)memex

$(OUT_EXE)memex: $(SUPPORT_HEADERS) $(MEMORY_HEADERS) $(SUPPORT_OBJS) $(MEMORY_OBJS) $(CPPEMIT_DIR)emit.cpp
	@mkdir -p $(OUT_EXE)
	$(CC) $(CFLAGS) -o $(OUT_EXE)memex $(SUPPORT_OBJS) $(MEMORY_OBJS) $(CPPEMIT_DIR)emit.cpp

$(OUT_OBJ)gc.o: $(SUPPORT_HEADERS) $(MEMORY_HEADERS) $(MEMORY_DIR)gc.cpp
	@mkdir -p $(OUT_OBJ)
	$(CC) $(CFLAGS) -o $(OUT_OBJ)gc.o -c $(MEMORY_DIR)gc.cpp

$(OUT_OBJ)threadinfo.o: $(SUPPORT_HEADERS) $(MEMORY_HEADERS) $(MEMORY_DIR)threadinfo.cpp
	@mkdir -p $(OUT_OBJ)
	$(CC) $(CFLAGS) -o $(OUT_OBJ)threadinfo.o -c $(MEMORY_DIR)threadinfo.cpp

$(OUT_OBJ)allocator.o: $(SUPPORT_HEADERS) $(MEMORY_HEADERS) $(MEMORY_DIR)allocator.cpp
	@mkdir -p $(OUT_OBJ)
	$(CC) $(CFLAGS) -o $(OUT_OBJ)allocator.o -c $(MEMORY_DIR)allocator.cpp

$(OUT_OBJ)xalloc.o: $(SUPPORT_HEADERS) $(SUPPORT_DIR)xalloc.cpp
	@mkdir -p $(OUT_OBJ)
	$(CC) $(CFLAGS) -o $(OUT_OBJ)xalloc.o -c $(SUPPORT_DIR)xalloc.cpp

$(OUT_OBJ)common.o: $(SUPPORT_HEADERS) $(RUNTIME_DIR)common.cpp
	@mkdir -p $(OUT_OBJ)
	$(CC) $(CFLAGS) -o $(OUT_OBJ)common.o -c $(RUNTIME_DIR)common.cpp

clean:
	rm -rf $(OUT_EXE)
