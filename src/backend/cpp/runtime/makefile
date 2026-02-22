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

#dev is default, for another flavor : make BUILD=release/debug/test
BUILD := dev

#also support epsilon to disable gc
ALLOC := gc

CC=g++
CSTDFLAGS=-Wall -Wextra -Wno-unused-parameter -Wuninitialized -Werror -std=gnu++20 -fno-exceptions -fno-rtti -fno-strict-aliasing -fno-omit-frame-pointer -fno-stack-protector -Wshadow -Weffc++

INTERNAL_FLAGS.gc= 
INTERNAL_FLAGS.epsilon=-DEPSILON

OPTIONS=

CFLAGS_OPT.test=-O0 -g -ggdb -DBSQ_GC_TESTING -DMEM_STATS -DBSQ_GC_CHECK_ENABLED -DVERBOSE_HEADER
CFLAGS_OPT.debug=-O0 -g -ggdb -DMEM_STATS -DBSQ_GC_CHECK_ENABLED -DVERBOSE_HEADER
CFLAGS_OPT.dev=-O0 -g -ggdb
CFLAGS_OPT.release=-O2 -march=x86-64-v3
CFLAGS=${CFLAGS_OPT.${BUILD}} ${OPTIONS} ${CSTDFLAGS} ${INTERNAL_FLAGS.${ALLOC}}

SUPPORT_HEADERS=$(RUNTIME_DIR)common.h $(SUPPORT_DIR)memstats.h $(SUPPORT_DIR)xalloc.h $(SUPPORT_DIR)epsilon.h $(SUPPORT_DIR)arraylist.h $(SUPPORT_DIR)pagetable.h $(SUPPORT_DIR)qsort.h
SUPPORT_SOURCES=$(RUNTIME_DIR)common.cpp  $(SUPPORT_DIR)memstats.cpp $(SUPPORT_DIR)xalloc.cpp $(SUPPORT_DIR)epsilon.cpp
SUPPORT_OBJS=$(OUT_OBJ)common.o $(OUT_OBJ)memstats.o $(OUT_OBJ)xalloc.o $(OUT_OBJ)epsilon.o

MEMORY_HEADERS=$(RUNTIME_DIR)common.h $(MEMORY_DIR)allocator.h $(MEMORY_DIR)threadinfo.h $(MEMORY_DIR)decsprcsr.h $(MEMORY_DIR)gc.h
MEMORY_SOURCES=$(MEMORY_DIR)allocator.cpp $(MEMORY_DIR)threadinfo.cpp $(MEMORY_DIR)decsprcsr.cpp $(MEMORY_DIR)gc.cpp
MEMORY_OBJS=$(OUT_OBJ)allocator.o $(OUT_OBJ)threadinfo.o $(MEMORY_DIR)decsprcsr.o $(OUT_OBJ)gc.o 

CPPEMIT_HEADERS=$(CPPEMIT_DIR)cppruntime.hpp
CPPEMIT_OBJS=$(OUT_OBJ)cppruntime.o

#if we built with epsilon allocator enabled clean first
ifeq ($(ALLOC), epsilon)
NEED_CLEAN=clean
else
NEED_CLEAN=
endif

all: $(NEED_CLEAN) $(OUT_EXE)memex

# Only builds the GC by executing a temporary file that does nothing
gc: $(SUPPORT_HEADERS) $(MEMORY_HEADERS) $(CPPEMIT_HEADERS) $(SUPPORT_OBJS) $(MEMORY_OBJS) $(CPPEMIT_OBJS)
	@mkdir -p $(OUT_EXE)
	@echo "int main() { return 0; }" > $(OUT_EXE)gcmain.cpp
	$(CC) $(CFLAGS) -o $(OUT_EXE)gctest $(SUPPORT_OBJS) $(MEMORY_OBJS) $(CPPEMIT_OBJS) $(OUT_EXE)gcmain.cpp
	@rm $(OUT_EXE)gcmain.cpp
	@rm $(OUT_EXE)gctest

$(OUT_EXE)memex: $(SUPPORT_HEADERS) $(MEMORY_HEADERS) $(CPPEMIT_HEADERS) $(SUPPORT_OBJS) $(MEMORY_OBJS) $(CPPEMIT_OBJS) $(CPPEMIT_DIR)emit.cpp
	@mkdir -p $(OUT_EXE)
	$(CC) $(CFLAGS) -o $(OUT_EXE)memex $(SUPPORT_OBJS) $(MEMORY_OBJS) $(CPPEMIT_OBJS) $(CPPEMIT_DIR)emit.cpp

$(OUT_OBJ)gc.o: $(SUPPORT_HEADERS) $(MEMORY_HEADERS) $(MEMORY_DIR)gc.cpp
	@mkdir -p $(OUT_OBJ)
	$(CC) $(CFLAGS) -o $(OUT_OBJ)gc.o -c $(MEMORY_DIR)gc.cpp

$(OUT_OBJ)threadinfo.o: $(SUPPORT_HEADERS) $(MEMORY_HEADERS) $(MEMORY_DIR)threadinfo.cpp
	@mkdir -p $(OUT_OBJ)
	$(CC) $(CFLAGS) -o $(OUT_OBJ)threadinfo.o -c $(MEMORY_DIR)threadinfo.cpp

$(OUT_OBJ)allocator.o: $(SUPPORT_HEADERS) $(MEMORY_HEADERS) $(MEMORY_DIR)allocator.cpp
	@mkdir -p $(OUT_OBJ)
	$(CC) $(CFLAGS) -o $(OUT_OBJ)allocator.o -c $(MEMORY_DIR)allocator.cpp

$(OUT_OBJ)decsprcsr.o: $(SUPPORT_HEADERS) $(MEMORY_HEADERS) $(MEMORY_DIR)decsprcsr.cpp
	@mkdir -p $(OUT_OBJ)
	$(CC) $(CFLAGS) -o $(OUT_OBJ)decsprcsr.o -c $(MEMORY_DIR)decsprcsr.cpp

$(OUT_OBJ)epsilon.o: $(SUPPORT_HEADERS) $(SUPPORT_DIR)epsilon.cpp 
	@mkdir -p $(OUT_OBJ)
	$(CC) $(CFLAGS) -o $(OUT_OBJ)epsilon.o -c $(SUPPORT_DIR)epsilon.cpp

$(OUT_OBJ)xalloc.o: $(SUPPORT_HEADERS) $(SUPPORT_DIR)xalloc.cpp
	@mkdir -p $(OUT_OBJ)
	$(CC) $(CFLAGS) -o $(OUT_OBJ)xalloc.o -c $(SUPPORT_DIR)xalloc.cpp

$(OUT_OBJ)memstats.o: $(SUPPORT_HEADERS) $(SUPPORT_DIR)memstats.cpp
	@mkdir -p $(OUT_OBJ)
	$(CC) $(CFLAGS) -o $(OUT_OBJ)memstats.o -c $(SUPPORT_DIR)memstats.cpp

$(OUT_OBJ)common.o: $(SUPPORT_HEADERS) $(RUNTIME_DIR)common.cpp
	@mkdir -p $(OUT_OBJ)
	$(CC) $(CFLAGS) -o $(OUT_OBJ)common.o -c $(RUNTIME_DIR)common.cpp

$(OUT_OBJ)cppruntime.o: $(CPPEMIT_HEADERS) $(CPPEMIT_DIR)cppruntime.cpp 
	@mkdir -p $(OUT_OBJ)
	$(CC) $(CFLAGS) -o $(OUT_OBJ)cppruntime.o -c $(CPPEMIT_DIR)cppruntime.cpp

clean:
	rm -rf $(OUT_EXE)
