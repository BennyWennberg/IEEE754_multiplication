# Makefile for Writing Make Files Example
#
# *****************************************************
# Variables to control Makefile operation

CC = g++
CFLAGS = -Wall -g

# ****************************************************
# Targets needed to bring the executable up to date

run: main.o bfloat_multiplication.o
	$(CC) $(CFLAGS) -o run  main.o bfloat_multiplication.o

main.o: main.cpp
	$(CXX) $(CXXFLAGS) -c main.cpp

bfloat_multiplication.o: bachelor.hpp

clean:
	rm -f *.o bfloat_multiplication main
