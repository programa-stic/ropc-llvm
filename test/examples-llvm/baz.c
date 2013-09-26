#include <stdio.h>
#include "llvm_intrinsics.h"

int main() {
	char fmt[] = "%d\n";
	int x = 1 + 1 + 1;

	while (x != 10) {
		printf(fmt, x);
		x = x + 1;
	}

	return 0;
}
