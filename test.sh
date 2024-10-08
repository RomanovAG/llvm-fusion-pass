#!/bin/bash

CLANG="./../build/bin/clang-20"
OPT="./../build/bin/opt"
INPUT_FILE="./tests/fusion-manyloops-input.c"
PLUGIN_PATH="./build/libfusion-pass.so"

EXE_INPUT="fusion-manyloops-input.bin"
EXE_OUTPUT="fusion-manyloops-output.bin"
LL_INPUT="fusion-manyloops-input.ll"
LL_OUTPUT="fusion-manyloops-output.ll"

DEBUG_FILE="debug.txt"

> $DEBUG_FILE

$CLANG -O0 -Xclang -disable-O0-optnone $INPUT_FILE -o $EXE_INPUT
if [ $? -ne 0 ]; then
    echo "First program compilation failed."
    exit 1
fi

$CLANG -O0 -Xclang -disable-O0-optnone -S -emit-llvm $INPUT_FILE -o $LL_INPUT
if [ $? -ne 0 ]; then
    echo "LLVM IR generation failed."
    exit 1
fi

$OPT -S -passes=mem2reg $LL_INPUT -o $LL_INPUT
if [ $? -ne 0 ]; then
    echo "mem2reg pass failed."
    exit 1
fi

$OPT -load-pass-plugin $PLUGIN_PATH -passes=fusion-pass -debug -S $LL_INPUT -o $LL_OUTPUT 2>> $DEBUG_FILE
if [ $? -ne 0 ]; then
    echo "Fusion pass failed."
    exit 1
fi

$CLANG -O0 -Xclang -disable-O0-optnone $LL_OUTPUT -o $EXE_OUTPUT
if [ $? -ne 0 ]; then
    echo "Second program compilation failed."
    exit 1
fi

./$EXE_INPUT > res_input.txt
./$EXE_OUTPUT > res_output.txt
diff res_input.txt res_output.txt > diff_output.txt

rm $EXE_INPUT
rm $EXE_OUTPUT

if [ ! -s diff_output.txt ]; then
    echo "Test passed: The outputs are identical."
else
    echo "Test failed: The outputs differ. Check diff_output.txt for details."
fi

