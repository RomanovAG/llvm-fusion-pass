**0:**
-
Clone this repository to llvm-project repository.

**1:**
-
To compile the library run these commands.
```
$ export LLVM_DIR=<path to llvm-project/build>
$ cd llvm-fusion-pass/build
$ cmake -DLT_LLVM_INSTALL_DIR=$LLVM_DIR
$ make
```
**2.1**
-
If you want to skip all preparations and test lib instead, run *test.sh* and check *.ll* files and output produced by compiled programs.
```
$ cd llvm-fusion-pass
$ bash test.sh
```
Also check *debug.txt* which contains useful info.

**2.2:**
-
Here's some useful commands if you want manually investigate code.\
Use `-debug` flag while running *opt* with `fusion-pass` to see which loops it fused.
```
$ cd llvm-project
$ ./build/bin/clang-20 -O0 -Xclang -disable-O0-optnone -S -emit-llvm ./llvm-fusion-pass/tests/fusion-manyloops-input.c -o fusion-manyloops-input.ll
$ ./build/bin/opt -S -passes="mem2reg" fusion-manyloops-input.ll -o fusion-manyloops-input.ll
$ ./build/bin/opt -load-pass-plugin ./llvm-fusion-pass/build/libfusion-pass.so -passes=fusion-pass -debug -S fusion-manyloops-input.ll -o fusion-manyloops-output.ll
$ ./build/bin/opt -passes='print<loops>' -disable-output fusion-manyloops-output.ll 
```
**3:**
-
Flags:\
`-debug`\
`-allow-throw` -- allow fusion for loops that might throw exceptions.