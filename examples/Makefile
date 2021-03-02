
install:
	(cd ..; gradle installDist --parallel)

IfThenElse: install
	../build/install/mini-symex/bin/mini-symex IfThenElse.txt

SimpleLoop: install
	../build/install/mini-symex/bin/mini-symex SimpleLoop.txt