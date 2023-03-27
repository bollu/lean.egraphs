.PHONY: run compile_commands
all: run

run: egg
	ASAN_OPTIONS=detect_leaks=0 ./egg

egg: egg.cpp
	g++ -g -std=c++14 -fsanitize=address -fsanitize=undefined egg.cpp -o egg

compile_commands:
	bear -- make all
