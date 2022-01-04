syntax.lua: syntax.ml
	amc compile syntax.ml -o syntax.lua

clean:
	rm *.lua

PHONY: clean
