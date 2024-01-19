#ifndef _MY_CLASS_
#define _MY_CLASS_

//#define _GLIBCXX_USE_CXX11_ABI 0/1

#include <cstring>
#include <fstream>
#include <iostream>
#include <stdio.h>
#include <stdlib.h>
#include <string>

using std::fstream;
using namespace std;
 

// creating smt-lib2 code für bfloat8
int bv(string sizebit, int sign, int exponent, int mantissa);
int bv_bv(string sizebit, int sign, int exponent, int mantissa);
int fp_fp(string sizebit);
int bv_fp(string sizebit, int sign, int exponent,int mantissa);
#endif
