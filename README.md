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
$ ./build/bin/clang-20 -O0 -Xclang -disable-O0-optnone -S -emit-llvm ./llvm-fusion-pass/tests/cpp-input.cpp -o cpp-input.ll
$ ./build/bin/opt -S -passes="mem2reg" fusion-input.ll -o fusion-input.ll
$ ./build/bin/opt -load-pass-plugin ./llvm-fusion-pass/build/libfusion-pass.so -passes=fusion-pass -S fusion-input.ll -o fusion-output.ll
$ ./build/bin/opt -passes='print<loops>' -disable-output fusion-output.ll 
```
