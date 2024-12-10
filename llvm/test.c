#include <stdio.h>

// compile with:
// clang-18 -O0 -Xclang -disable-O0-optnone -emit-llvm -S test.c
//
// run mem2reg with:
// opt-18 -passes="mem2reg" -o test.ll test.ll
//
// run with:
// opt-18 -load-pass-plugin=./build/loop-opt/LoopPass.so
// -passes="custom-loop-pass" -disable-output test.ll

void do_smth() {
  int a = 10;
  int b = 20;

  for (int i = 0; i < 10; ++i) {
    int c = a * b;
  }
}

int main(void) {
  do_smth();
  return 0;
}
