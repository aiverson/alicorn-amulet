syntax-tests.lua: syntax-tests.ml syntax.ml ast.ml # add other deps?
	amc compile syntax-tests.ml -o syntax-tests.lua

clean:
	rm *.lua

PHONY: clean
