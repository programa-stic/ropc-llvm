#include <stdio.h>
#include "llvm_intrinsics.h"

void fib(int n, int * out) {
    int x = 0;
    int y = 0;

    if (n == 0 || n == 1) {
        *out = n;

        return;
    }

    fib(n-1, &x);
    fib(n-2, &y);

    *out = x + y;

    return;
}

int main() {
    char fmt[] = "%d\n";
    int i = 0;
    int x = 0;

    while (i != 11) {
        fib(i, &x);
        printf(fmt, x);
        i = i + 1;
    }

    return 0;
}

