// RUN: %sotoc-transform-compile
// RUN: %run-on-host | %filecheck %s

#include <stdio.h>

int main(void) {

  int i;
  int j;
  int k;
  int x[2][5][10] = {{{2, 3, 5, 7, 11, 13, 17, 23, 29, 31},
                      {2, 3, 5, 7, 11, 13, 17, 23, 29, 31},
                      {2, 3, 5, 7, 11, 13, 17, 23, 29, 31},
                      {2, 3, 5, 7, 11, 13, 17, 23, 29, 31},
                      {2, 3, 5, 7, 11, 13, 17, 23, 29, 31}},
                     {{2, 3, 5, 7, 11, 13, 17, 23, 29, 31},
                      {2, 3, 5, 7, 11, 13, 17, 23, 29, 31},
                      {2, 3, 5, 7, 11, 13, 17, 23, 29, 31},
                      {2, 3, 5, 7, 11, 13, 17, 23, 29, 31},
                      {2, 3, 5, 7, 11, 13, 17, 23, 29, 31}}};
  int y[2][5][10] = {{{31, 29, 23, 17, 13, 11, 7, 5, 3, 2},
                      {31, 29, 23, 17, 13, 11, 7, 5, 3, 2},
                      {31, 29, 23, 17, 13, 11, 7, 5, 3, 2},
                      {31, 29, 23, 17, 13, 11, 7, 5, 3, 2},
                      {31, 29, 23, 17, 13, 11, 7, 5, 3, 2}},
                     {{31, 29, 23, 17, 13, 11, 7, 5, 3, 2},
                      {31, 29, 23, 17, 13, 11, 7, 5, 3, 2},
                      {31, 29, 23, 17, 13, 11, 7, 5, 3, 2},
                      {31, 29, 23, 17, 13, 11, 7, 5, 3, 2},
                      {31, 29, 23, 17, 13, 11, 7, 5, 3, 2}}};
  int a = 5;
  int z[2][5][10];

#pragma omp target parallel for simd device(0) map(tofrom                      \
                                                   : x, y) map(from            \
                                                               : z)            \
    map(to                                                                     \
        : a) private(j,k)
  for (i = 0; i < 2; i++) {
    for (j = 0; j < 5; j++) {
      for (k = 0; k < 10; k++) {
        z[i][j][k] = x[i][j][k] + a * y[i][j][k];
      }
    }
  }

  for (i = 0; i < 2; i++) {
    for (j = 0; j < 5; j++) {
      for (k = 0; k < 10; k++) {
        printf(" %d ", z[i][j][k]);
      }
      printf("\n");
    }
    printf("\n");
  }

  return 0;
}

// CHECK: 157  148  120  92  76  68  52  48  44  41 {{[[:space:]]+}} 157  148  120  92  76  68  52  48  44  41 {{[[:space:]]+}} 157  148  120  92  76  68  52  48  44  41 {{[[:space:]]+}} 157  148  120  92  76  68  52  48  44  41 {{[[:space:]]+}} 157  148  120  92  76  68  52  48  44  41 {{[[:space:]]+}} 157  148  120  92  76  68  52  48  44  41 {{[[:space:]]+}} 157  148  120  92  76  68  52  48  44  41 {{[[:space:]]+}} 157  148  120  92  76  68  52  48  44  41 {{[[:space:]]+}} 157  148  120  92  76  68  52  48  44  41 {{[[:space:]]+}} 157  148  120  92  76  68  52  48  44  41 {{[[:space:]]+}}
