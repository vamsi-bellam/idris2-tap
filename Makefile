.PHONY: clean build test
.SILENT: clean test

clean: 
	echo "Removing build folder.."; rm -rf build

build: 
	idris2 --build parser.ipkg

test:
	idris2 --build test.ipkg
	echo "Running Tests...\n"
	build/exec/runtests
	make clean
