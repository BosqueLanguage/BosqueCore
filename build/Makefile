MAKE_PATH=$(realpath $(dir $(lastword $(MAKEFILE_LIST))))
SRC_DIR=$(MAKE_PATH)/runcpp/
CORE_SRC_DIR=$(SRC_DIR)core/
RUNTIME_SRC_DIR=$(SRC_DIR)runtime/
ALLOC_SRC_DIR=$(RUNTIME_SRC_DIR)allocator/
BSQIR_SRC_DIR=$(RUNTIME_SRC_DIR)bsqir/

OUT_OBJ=$(BUILD_DIR)output/obj/

BUILD := unittests

CPPFLAGS_OPT.unittests=-Og -g -ggdb -DRB_INVARIANT_VALIDATE
CPPFLAGS_STD=-Wall -Wextra -Wno-unused-parameter -Wno-unused-variable -Wno-unused-but-set-variable -Wuninitialized -Werror -std=gnu++23 -fno-omit-frame-pointer -fno-exceptions -fno-rtti -fno-strict-aliasing -fno-stack-protector
        
CPPFLAGS=${CPPFLAGS_OPT.${BUILD}} ${CPPFLAGS_STD}

HEADERS=$(wildcard $(SRC_DIR)*.h) $(wildcard $(CORE_SRC_DIR)*.h) $(wildcard $(RUNTIME_SRC_DIR)*.h) $(wildcard $(ALLOC_SRC_DIR)*.h) $(wildcard $(BSQIR_SRC_DIR)*.h)
CPP=$(wildcard $(SRC_DIR)*.cpp) $(wildcard $(CORE_SRC_DIR)*.cpp) $(wildcard $(RUNTIME_SRC_DIR)*.cpp) $(wildcard $(ALLOC_SRC_DIR)*.cpp) $(wildcard $(BSQIR_SRC_DIR)*.cpp)
OBJ=$(OUT_OBJ)common.o $(OUT_OBJ)strings.o $(OUT_OBJ)memstats.o $(OUT_OBJ)gc_validation.o $(OUT_OBJ)alloc.o $(OUT_OBJ)gc.o $(OUT_OBJ)emit.o $(OUT_OBJ)lexer.o $(OUT_OBJ)parser.o

MAKEFLAGS += -j8

all: $(OBJ)

$(OUT_OBJ)common.o: $(HEADERS) $(CPP)
	@mkdir -p $(OUT_OBJ)
	g++ $(CPPFLAGS) -o $(OUT_OBJ)common.o -c $(SRC_DIR)common.cpp

$(OUT_OBJ)strings.o: $(HEADERS) $(CPP)
	@mkdir -p $(OUT_OBJ)
	g++ $(CPPFLAGS) -o $(OUT_OBJ)strings.o -c $(CORE_SRC_DIR)strings.cpp

$(OUT_OBJ)memstats.o: $(HEADERS) $(CPP)
	@mkdir -p $(OUT_OBJ)
	g++ $(CPPFLAGS) -o $(OUT_OBJ)memstats.o -c $(ALLOC_SRC_DIR)memstats.cpp

$(OUT_OBJ)gc_validation.o: $(HEADERS) $(CPP)
	@mkdir -p $(OUT_OBJ)
	g++ $(CPPFLAGS) -o $(OUT_OBJ)gc_validation.o -c $(ALLOC_SRC_DIR)gc_validation.cpp

$(OUT_OBJ)alloc.o: $(HEADERS) $(CPP)
	@mkdir -p $(OUT_OBJ)
	g++ $(CPPFLAGS) -o $(OUT_OBJ)alloc.o -c $(ALLOC_SRC_DIR)alloc.cpp

$(OUT_OBJ)gc.o: $(HEADERS) $(CPP)
	@mkdir -p $(OUT_OBJ)
	g++ $(CPPFLAGS) -o $(OUT_OBJ)gc.o -c $(ALLOC_SRC_DIR)gc.cpp

$(OUT_OBJ)emit.o: $(HEADERS) $(CPP)
	@mkdir -p $(OUT_OBJ)
	g++ $(CPPFLAGS) -o $(OUT_OBJ)emit.o -c $(BSQIR_SRC_DIR)emit.cpp

$(OUT_OBJ)lexer.o: $(HEADERS) $(CPP)
	@mkdir -p $(OUT_OBJ)
	g++ $(CPPFLAGS) -o $(OUT_OBJ)lexer.o -c $(BSQIR_SRC_DIR)lexer.cpp

$(OUT_OBJ)parser.o: $(HEADERS) $(CPP)
	@mkdir -p $(OUT_OBJ)
	g++ $(CPPFLAGS) -o $(OUT_OBJ)parser.o -c $(BSQIR_SRC_DIR)parser.cpp

clean:
	rm -rf $(OUT_OBJ)