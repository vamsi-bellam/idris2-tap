.PHONY: clean build test

clean: 
	echo "Removing build folder.."; rm -rf build

build: 
	idris2 --build parser.ipkg

test:
	idris2 --build test.ipkg
	build/exec/runtests
	make clean
