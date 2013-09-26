# ROPC-LLVM

Compilador **ROPC** refactorizado y modificado para soportar un subconjunto
básico del lenguaje intermedio de **LLVM**.

Antes de usarlo:

* Hay que compilar la libería BAP. Ver lib/bap-0.4/INSTALL para más información.
* Instalar un SMT solver (STP).
* Instalar clang.

Para compilar un programa de prueba:

    $ cd src
    $ make
    $ cd ../test/examples-llvm
    $ make
    $ cd ..
    $ make test-llvm

Luego de que un programa es *explotado*, termina en *segmentation fault*.

# Advertencia

Esto es un PoC, no esperar que ande sin modificaciones sobre un binario *real*.

Hay algunos problemas conocidos que están comentados en el código, referirse
a ellos para más información.

# Más Información

* README.ROPC
* ROPC : http://github.com/pakt/ropc
* STP : http://sourceforge.net/projects/stp-fast-prover/files/STP2/
