.PHONY: run compile_commands
all: run

run: egg
	./egg

egg: egg.cpp
	g++ -g -std=c++14 -fsanitize=address -fsanitize=undefined egg.cpp -o egg

compile_commands:
	bear -- make all
