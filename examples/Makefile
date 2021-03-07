Z3="| z3 -in -smt2 | grep -E '^sat$' || exit 1"

install:
	(cd ..; gradle installDist --parallel)

IfThenElse: install
	../build/install/mini-symex/bin/mini-symex IfThenElse.txt

LoopInit: install
	../build/install/mini-symex/bin/mini-symex LoopInit.txt

SimpleLoop: install
	../build/install/mini-symex/bin/mini-symex SimpleLoop.txt $(Z3)

Fib: install
	../build/install/mini-symex/bin/mini-symex Fib.txt