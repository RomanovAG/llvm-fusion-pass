**1:**
```
$ export LLVM_DIR=<path to llvm-project/build>
$ cd llvm-fusion-pass/build
$ cmake -DLT_LLVM_INSTALL_DIR=$LLVM_DIR
$ make
```
**2:**
```
$ cd llvm-project
$ ./build/bin/clang-20 -O0 -S -emit-llvm ./llvm-fusion-pass/tests/fusion-input.c -o fusion-input.ll
$ ./build/bin/opt -load-pass-plugin ./llvm-fusion-pass/build/libfusion-pass.so -passes=fusion-pass -disable-output fusion-input.ll
```
