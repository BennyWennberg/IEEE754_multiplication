#include <iostream>
#include "bachelor.hpp"

using namespace std;

int main() {
        int val1 = 1;
        int val2 = 1;
	string sizebit;
	string benchmark;
	int sign;
	int exponent;
	int mantissa;
	cout << "'1' for BV, '2' for BV_BV, '3' for FP_FP, '4' for BV_FP: ";
	cin >> benchmark;

    while (benchmark != "1" && benchmark != "2" && benchmark != "3" && benchmark != "4") {
        cout << "Invalid bitsize. Please enter '1' for BV, '2' for BV_BV, '3' for FP_FP, '4' for BV_FP: ";
        cin >> benchmark;
    }
        cout << "Please enter the size of bits: ";
        cin >>  sizebit;

    while (sizebit != "16" && sizebit != "32" && sizebit != "64" && sizebit != "128") {
        cout << "Invalid bitsize. Please enter a valid bitsize (16, 32, 64, 128): ";
        cin >> sizebit;
    }

        if(sizebit == "16") {
		sign = 1;
		exponent = 5;
		mantissa = 10;
        } else if(sizebit == "32") {
                sign = 1;
                exponent = 8;
                mantissa = 23;
               
	} else if(sizebit == "64") {
                sign = 1;
                exponent = 11;
                mantissa = 52;
               
        } else if(sizebit == "128") {
                sign = 1;
                exponent = 15;
                mantissa = 112;
        }
	if(benchmark == "1") {
		val1 = bv(sizebit, sign, exponent, mantissa);
	} else if(benchmark == "2") {
                val1 = bv_bv(sizebit, sign, exponent, mantissa);
        } else if(benchmark == "3") {
                val1 = fp_fp(sizebit);
        } else if(benchmark == "4") {
                val1 = bv_fp(sizebit, sign, exponent, mantissa);
        };
        cout << "Calculate Sizebite: "+sizebit << endl;
        return 0;
}
