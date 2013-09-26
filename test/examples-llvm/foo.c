#include <stdio.h>

void foo() {
	int x = 1;
}

int main() {
	int one = 1;
	int odd = 0;
	int even = 0;
	int i = 0;
	int n = 10;
	int r = 0;
	int total = 0;

sum:
	foo();
	r = i & 1;
	if (r == 1) goto odd;
	even = even + i;
	goto skip;

odd:
	odd = odd + i;

skip:
	i = i + 1;
	if (i != n) goto sum;
	total = odd + even;

	return 0;
}