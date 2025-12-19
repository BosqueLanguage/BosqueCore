MAKE_PATH=$(realpath $(dir $(lastword $(MAKEFILE_LIST))))
BUILD_DIR=$(MAKE_PATH)/../
SRC_DIR=$(MAKE_PATH)/

CORE_SRC_DIR=$(SRC_DIR)core/
RUNTIME_SRC_DIR=$(SRC_DIR)runtime/
ALLOC_SRC_DIR=$(RUNTIME_SRC_DIR)allocator/
BSQIR_SRC_DIR=$(RUNTIME_SRC_DIR)bsqir/

OUT_COMPONENTS=$(BUILD_DIR)output/
OUT_OBJ=$(BUILD_DIR)output/obj/

JSON_INCLUDES=-I $(BUILD_DIR)include/json/

#dev is default, for another flavor : make BUILD=release or debug
BUILD := debug

CPP=g++ 
CPP_STDFLAGS=-Wall -Wextra -Wno-unused-parameter -Wuninitialized -Werror -std=gnu++20 -fno-exceptions -fno-rtti -fno-strict-aliasing -fno-stack-protector -fPIC

CPPFLAGS_OPT.debug=-O0 -g -ggdb -fno-omit-frame-pointer -fsanitize=address
CPPFLAGS_OPT.dev=-O0 -g -ggdb -fno-omit-frame-pointer
CPPFLAGS_OPT.release=-O3 -march=x86-64-v3
CPPFLAGS=${CPPFLAGS_OPT.${BUILD}} ${CPP_STDFLAGS}

HEADERS=$(wildcard $(SRC_DIR)*.h) $(wildcard $(CORE_SRC_DIR)*.h) $(wildcard $(RUNTIME_SRC_DIR)*.h) $(wildcard $(ALLOC_SRC_DIR)*.h) $(wildcard $(BSQIR_SRC_DIR)*.h)
OBJS=$(OUT_OBJ)common.o $(OUT_OBJ)alloc.o $(OUT_OBJ)lexer.o $(OUT_OBJ)parser.o $(OUT_OBJ)emit.o

#MAKEFLAGS += -j4

all: $(OBJS)

${OUT_COMPONENTS}sbsq: $(HEADERS) $(OBJS) main.cpp
	@mkdir -p $(OUT_COMPONENTS)
	$(CPP) $(CPPFLAGS) -o ${OUT_COMPONENTS}sbsq $(OBJS) $(JSON_INCLUDES) main.cpp

$(OUT_OBJ)emit.o: $(HEADERS) $(BSQIR_SRC_DIR)emit.cpp
	@mkdir -p $(OUT_OBJ)
	$(CPP) $(CPPFLAGS) -o $(OUT_OBJ)emit.o -c $(BSQIR_SRC_DIR)emit.cpp

$(OUT_OBJ)parser.o: $(HEADERS) $(BSQIR_SRC_DIR)parser.cpp
	@mkdir -p $(OUT_OBJ)
	$(CPP) $(CPPFLAGS) -o $(OUT_OBJ)parser.o -c $(BSQIR_SRC_DIR)parser.cpp

$(OUT_OBJ)lexer.o: $(HEADERS) $(BSQIR_SRC_DIR)lexer.cpp
	@mkdir -p $(OUT_OBJ)
	$(CPP) $(CPPFLAGS) -o $(OUT_OBJ)lexer.o -c $(BSQIR_SRC_DIR)lexer.cpp

$(OUT_OBJ)alloc.o: $(HEADERS) $(ALLOC_SRC_DIR)alloc.cpp
	@mkdir -p $(OUT_OBJ)
	$(CPP) $(CPPFLAGS) -o $(OUT_OBJ)alloc.o -c $(ALLOC_SRC_DIR)alloc.cpp

$(OUT_OBJ)common.o: $(HEADERS) $(SRC_DIR)common.cpp
	@mkdir -p $(OUT_OBJ)
	$(CPP) $(CPPFLAGS) -o $(OUT_OBJ)common.o -c $(SRC_DIR)common.cpp

clean:
	rm -rf $(OUT_OBJ)*
	rm -rf $(OUT_COMPONENTS)*