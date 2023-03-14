.PHONY: run
all: run

run: egg
	./egg 

egg: egg.cpp
	g++ -std=c++14 -fsanitize=address -fsanitize=undefined egg.cpp -o egg
