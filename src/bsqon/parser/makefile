MAKE_PATH=$(realpath $(dir $(lastword $(MAKEFILE_LIST))))
BUILD_DIR=$(MAKE_PATH)/../../../build/
SRC_DIR=$(MAKE_PATH)/
BSQON_CFG_DIR=$(SRC_DIR)lb/

OUT_EXE=$(BUILD_DIR)output/
OUT_OBJ=$(BUILD_DIR)output/obj/

JSON_INCLUDES=-I $(BUILD_DIR)include/headers/json/

CC=gcc
CFLAGS=-g -ggdb -DEXPORT

CPP=g++
CPPFLAGS=-g -ggdb -fno-omit-frame-pointer -Wall -Wextra -Wno-unused-parameter -Wuninitialized -Werror -std=c++20 -fsanitize=address

CFG_SOURCES=$(BSQON_CFG_DIR)bsqon.y $(BSQON_CFG_DIR)bsqon.l

PARSER_HEADERS=$(BSQON_CFG_DIR)bytestring.h $(BSQON_CFG_DIR)bsqon_type_ast.h $(BSQON_CFG_DIR)bsqon_ast.h $(BSQON_CFG_DIR)bsqon.tab.h
PARSER_SOURCES=$(BSQON_CFG_DIR)bytestring.c $(BSQON_CFG_DIR)bsqon_type_ast.c $(BSQON_CFG_DIR)bsqon_ast.c $(BSQON_CFG_DIR)bsqon.tab.c $(BSQON_CFG_DIR)lex.yy.c
PARSER_OBJS=$(OUT_OBJ)bytestring.o $(OUT_OBJ)bsqon_type_ast.o $(OUT_OBJ)bsqon_ast.o $(OUT_OBJ)bsqon.tab.o $(OUT_OBJ)lex.yy.o

BSQON_HEADERS=$(SRC_DIR)../common.h $(SRC_DIR)../regex/bsqregex.h $(SRC_DIR)../regex/bsqpath.h $(SRC_DIR)../info/type_info.h $(SRC_DIR)../info/bsqon.h $(SRC_DIR)bsqon_parse.h
BSQON_SOURCES=$(SRC_DIR)../common.cpp $(SRC_DIR)../regex/bsqregex.cpp $(SRC_DIR)../info/type_info.cpp $(SRC_DIR)../info/bsqon.cpp $(SRC_DIR)bsqon_parse.cpp $(SRC_DIR)bsqon_main.cpp

MAKEFLAGS += -j4

all: bsqon bsqon_parser

cfg:
	flex -o $(BSQON_CFG_DIR)lex.yy.c $(BSQON_CFG_DIR)bsqon.l
	bison -d -Wcex -o $(BSQON_CFG_DIR)bsqon.tab.c $(BSQON_CFG_DIR)bsqon.y

bsqon: $(BSQON_HEADERS) $(BSQON_SOURCES) $(PARSER_OBJS)
	@mkdir -p $(OUT_EXE)
	$(CPP) $(CPPFLAGS) $(JSON_INCLUDES) -o $(OUT_EXE)bsqon $(BSQON_SOURCES) $(PARSER_OBJS) -lfl -lgmp

bsqon_parser: $(PARSER_HEADERS) $(PARSER_SOURCES)
	@mkdir -p $(OUT_EXE)
	$(CC) -O1 -g -ggdb -fno-omit-frame-pointer -o $(OUT_EXE)bsqon_parser $(PARSER_SOURCES) -lfl

$(OUT_OBJ)bytestring.o: $(PARSER_HEADERS) $(PARSER_SOURCES)
	@mkdir -p $(OUT_OBJ)
	$(CC) $(CFLAGS) -o $(OUT_OBJ)bytestring.o -c $(BSQON_CFG_DIR)bytestring.c

$(OUT_OBJ)bsqon_type_ast.o: $(PARSER_HEADERS) $(PARSER_SOURCES)
	@mkdir -p $(OUT_OBJ)
	$(CC) $(CFLAGS) -o $(OUT_OBJ)bsqon_type_ast.o -c $(BSQON_CFG_DIR)bsqon_type_ast.c

$(OUT_OBJ)bsqon_ast.o: $(PARSER_HEADERS) $(PARSER_SOURCES)
	@mkdir -p $(OUT_OBJ)
	$(CC) $(CFLAGS) -o $(OUT_OBJ)bsqon_ast.o -c $(BSQON_CFG_DIR)bsqon_ast.c

$(OUT_OBJ)bsqon.tab.o: $(PARSER_HEADERS) $(PARSER_SOURCES)
	@mkdir -p $(OUT_OBJ)
	$(CC) $(CFLAGS) -o $(OUT_OBJ)bsqon.tab.o -c $(BSQON_CFG_DIR)bsqon.tab.c

$(OUT_OBJ)lex.yy.o: $(PARSER_HEADERS) $(PARSER_SOURCES)
	@mkdir -p $(OUT_OBJ)
	$(CC) $(CFLAGS) -o $(OUT_OBJ)lex.yy.o -c $(BSQON_CFG_DIR)lex.yy.c

clean:
	rm -rf $(OUT_EXE)bsqon $(OUT_EXE)bsqon_parser $(OUT_OBJ)*.o