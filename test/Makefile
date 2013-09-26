bin_dir := ../bin

all: test-llvm

asm: test.asm test.c
	nasm -felf32 test.asm -o asm.o
	gcc -ggdb -m32 asm.o test.c

gadgets: asm
	$(bin_dir)/gadget-bap-0.4 a.out candidates.bin
	$(bin_dir)/verify-bap-0.4 candidates.bin verified.bin
	rm -rf a.out.formula.txt

ropc-ropl: gadgets
	$(bin_dir)/ropc-bap-0.4 ropl examples-ropl/fib.ropl verified.bin

ropc-llvm: gadgets
	$(bin_dir)/ropc-bap-0.4 llvm examples-llvm/fib.S verified.bin

test-ropl: ropc-ropl
	./a.out compiled-ropl.bin

test-llvm: ropc-llvm
	./a.out compiled-llvm.bin

clean:
	rm -rf *.o a.out
	rm -rf candidates.bin verified.bin
	rm -rf a.out.formula.txt
	rm -rf compiled-ropl.bin compiled-llvm.bin
