OPTFLAGS = -O0
CFLAGS   = -emit-llvm -S

EXAMPLES = baz fib foo trivial

all: $(EXAMPLES)

baz: baz.c
	clang $(OPTFLAGS) $(CFLAGS) baz.c -o baz.S

fib: fib.c
	clang $(OPTFLAGS) $(CFLAGS) fib.c -o fib.S

foo: foo.c
	clang $(OPTFLAGS) $(CFLAGS) foo.c -o foo.S

trivial: trivial.c
	clang $(OPTFLAGS) $(CFLAGS) trivial.c -o trivial.S

clean:
	rm -rf *.S
