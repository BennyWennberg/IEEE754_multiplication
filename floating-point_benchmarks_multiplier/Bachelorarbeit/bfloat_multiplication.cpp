#include <iostream>
#include "bachelor.hpp"
#include <cmath>
#include <bitset>
using namespace std;

int bv(string sizebit, int sign, int exponent,int mantissa) {

        fstream smt2File;
        smt2File.open("BV"+sizebit+"_multiplication.smt2",ios::out);
        smt2File << ";;; bv"+sizebit+" multiplication" << endl;
        smt2File << "(set-option :produce-models true)" << endl;
        smt2File << "(set-logic QF_BV)" << endl; // Verwendung von QF_FPBV für Floating-Point Arithmetic
        smt2File << endl;
        smt2File << "(set-info :source |Benny Wennberg Bachelor thesis|)" << endl;        // ab hier Code

        // Schreiben von SMT2-Inhalten in die Datei

    // input variablen
    int signWidth = sign;
    int exponentWidth = exponent;
    int mantissaWidth = mantissa;
    int mant_length = mantissaWidth * 2;
    int length_max = stoi(sizebit);


    // Deklaration von festen Bit-Vektoren für Vorzeichen, Exponent und Mantisse für x, y und z
    smt2File <<  "(declare-fun eins () (_ BitVec " << signWidth << "))" << endl;
    smt2File << "(assert (= eins  #b1 ))" << endl;
    smt2File <<  "(declare-fun null () (_ BitVec " << signWidth << "))" << endl;
    smt2File << "(assert (= null  #b0 ))" << endl;

    smt2File <<  "(declare-fun compare_s () (_ BitVec " << mantissaWidth - 1<< "))" << endl;
    smt2File << "(assert (= compare_s  (_ bv0 " << mantissaWidth - 1<< ")))" << endl;

    smt2File << "(declare-fun comp_expo () (_ BitVec " << exponentWidth<<"))" << endl;
    smt2File << "(assert (= comp_expo  (_ bv0 " << exponentWidth << ")))" << endl;
    smt2File << "(declare-fun comp_mant () (_ BitVec " << mant_length + 2<<"))" << endl;
    smt2File << "(assert (= comp_mant  (_ bv0 " << mant_length + 2 << ")))" << endl;
    smt2File << "(declare-fun comp_mant_0 () (_ BitVec " << mantissaWidth<<"))" << endl;
    smt2File << "(assert (= comp_mant_0  (_ bv0 " << mantissaWidth << ")))" << endl;

    smt2File << "(declare-fun comp_expo_1 () (_ BitVec " << exponentWidth<<"))" << endl;
    smt2File << "(declare-fun comp_mant_1 () (_ BitVec " << mantissaWidth<<"))" << endl;
    if (length_max == 16) {
        smt2File << "(assert (= comp_mant_1 #b1111111111))" << endl;
        smt2File << "(assert (= comp_expo_1 #b11111))" << endl;
    } else if (length_max == 128) {
        smt2File << "(assert (= comp_mant_1 #b1111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111))" << endl;
        smt2File << "(assert (= comp_expo_1 #b111111111111111))" << std::endl;
    } else if (length_max == 32) {
         smt2File << "(assert (= comp_mant_1 #b11111111111111111111111))" << endl;
         smt2File << "(assert (= comp_expo_1 #b11111111))" << std::endl;
    } else if (length_max == 64) {
         smt2File << "(assert (= comp_mant_1 #b1111111111111111111111111111111111111111111111111111))" << endl;
         smt2File << "(assert (= comp_expo_1 #b11111111111))" << std::endl;
    }


    smt2File << "(declare-fun add_expo_0 () (_ BitVec " << exponentWidth - 1<<"))" << endl;
    smt2File << "(assert (= add_expo_0  (_ bv0 " << exponentWidth - 1 << ")))" << endl;
    smt2File << "(declare-fun add_expo () (_ BitVec " << exponentWidth <<"))" << endl;
    smt2File << "(assert (= add_expo (concat add_expo_0 eins)))" << endl;

    smt2File << "(declare-fun add_mant_0 () (_ BitVec " << mantissaWidth - 1<<"))" << endl;
    smt2File << "(assert (= add_mant_0  (_ bv0 " << mantissaWidth - 1 << ")))" << endl;
    smt2File << "(declare-fun add_mant () (_ BitVec " << mantissaWidth <<"))" << endl;
    smt2File << "(assert (= add_mant (concat add_mant_0 eins)))" << endl;


    smt2File << "(declare-fun add_shift_0 () (_ BitVec " << exponentWidth<<"))" << endl;
    smt2File << "(assert (= add_shift_0  (_ bv0 " << exponentWidth << ")))" << endl;
    smt2File << "(declare-fun add_shift () (_ BitVec " << exponentWidth + 1 <<"))" << endl;
    smt2File << "(assert (= add_shift (concat add_shift_0 eins)))" << endl;

    smt2File << "(declare-fun shift_mant_0 () (_ BitVec " << mant_length + 1<<"))" << endl;
    smt2File << "(assert (= shift_mant_0  (_ bv0 " << mant_length + 1 << ")))" << endl;
    smt2File << "(declare-fun shift_mant () (_ BitVec " << mant_length + 2<<"))" << endl;
    smt2File << "(assert (= shift_mant (concat shift_mant_0 eins)))" << endl;

    smt2File << "(declare-fun x () (_ BitVec " << length_max << "))" << endl;
    smt2File << "(declare-fun x_sign () (_ BitVec " << signWidth << "))" << endl;
    smt2File << "(declare-fun x_exponent () (_ BitVec " << exponentWidth << "))" << endl;
    smt2File << "(declare-fun x_mantissa () (_ BitVec " << mantissaWidth << "))" << endl;

    smt2File << "(declare-fun y () (_ BitVec " << length_max << "))" << endl;
    smt2File << "(declare-fun y_sign () (_ BitVec " << signWidth << "))" << endl;
    smt2File << "(declare-fun y_exponent () (_ BitVec " << exponentWidth << "))" << endl;
    smt2File << "(declare-fun y_mantissa () (_ BitVec " << mantissaWidth << "))" << endl;

        // extend Mantissa for multiplication
    smt2File << "(declare-fun x_exponent_extra () (_ BitVec " << exponentWidth + 1 << "))" << endl;
    smt2File << "(declare-fun y_exponent_extra () (_ BitVec " << exponentWidth + 1<< "))" << endl;
    smt2File << "(declare-fun z_exponent_extra_help () (_ BitVec " << exponentWidth + 1<< "))" << endl;
    smt2File << "(declare-fun z_exponent_extra () (_ BitVec " << exponentWidth + 1<< "))" << endl;

    // extend Mantissa for multiplication
    smt2File << "(declare-fun x_mantissa_extra () (_ BitVec " << mant_length + 2 << "))" << endl;
    smt2File << "(declare-fun y_mantissa_extra () (_ BitVec " << mant_length + 2<< "))" << endl;
    smt2File << "(declare-fun z_mantissa_extra () (_ BitVec " << mant_length + 2<< "))" << endl;


   // Get the extended Mantissa with beginning bit
    smt2File << "(declare-fun  nullen_0 () (_ BitVec " << mantissaWidth + 1 << "))" << endl;
    smt2File << "(assert (= nullen_0  (_ bv0 " << mantissaWidth + 1 << ")))" << endl;
    smt2File << "(declare-fun  nullen_1 () (_ BitVec " << mantissaWidth + 2 << "))" << endl;
    smt2File << "(assert (= nullen_1 (concat nullen_0 eins)))" << endl;

    smt2File << "(declare-fun  nullen_00 () (_ BitVec " << mantissaWidth + 2 << "))" << endl;
    smt2File << "(assert (= nullen_00 (_ bv0 " << mantissaWidth + 2 << ")))" << endl;

    // Z variablen
    smt2File << "(declare-fun z () (_ BitVec " << signWidth + exponentWidth << "))" << endl;
    smt2File << "(declare-fun z_finale () (_ BitVec " << length_max << "))" << endl;

    smt2File << "(declare-fun z_sign () (_ BitVec " << signWidth << "))" << endl;

    smt2File << "(declare-fun z_exponent () (_ BitVec " << exponentWidth << "))" << endl;
    smt2File << "(declare-fun z_exponent_GRS () (_ BitVec " << exponentWidth << "))" << endl;
    smt2File << "(declare-fun z_exponent_deNorm () (_ BitVec " << exponentWidth << "))" << endl;
    smt2File << "(declare-fun z_exponent_zero () (_ BitVec " << exponentWidth << "))" << endl;
    smt2File << "(declare-fun z_exponent_overflow () (_ BitVec " << exponentWidth << "))" << endl;
    smt2File << "(declare-fun z_exponent_underflow () (_ BitVec " << exponentWidth << "))" << endl;
    smt2File << "(declare-fun z_exponent_over () (_ BitVec " << exponentWidth << "))" << endl;

    smt2File << "(declare-fun z_mantissa () (_ BitVec " << mantissaWidth  << "))" << endl;
    smt2File << "(declare-fun z_mantissa_rest () (_ BitVec " << mantissaWidth  << "))" << endl;
    smt2File << "(declare-fun z_mantissa_GRS () (_ BitVec " << mantissaWidth  << "))" << endl;
    smt2File << "(declare-fun z_mantissa_zero () (_ BitVec " << mant_length + 2 << "))" << endl;
    smt2File << "(declare-fun z_mantissa_overflow () (_ BitVec " << mant_length + 2 << "))" << endl;
    smt2File << "(declare-fun z_mantissa_underflow_0 () (_ BitVec " << mant_length + 2 << "))" << endl;
    smt2File << "(declare-fun z_mantissa_NaN () (_ BitVec " << mantissaWidth << "))" << endl;


    // Addition hilfe Bias muss noch je nach Bitsize um (bei 32 bit um 127 abgezogen werden.)
    smt2File << "(declare-fun bias () (_ BitVec " << exponentWidth << "))" << endl;
    smt2File << "(declare-fun bias_inf_compare () (_ BitVec " << exponentWidth << "))" << endl;
    smt2File << "(declare-fun bias_extra () (_ BitVec " << exponentWidth +1<< "))" << endl;
    smt2File << "(declare-fun bias_compare_underflow () (_ BitVec " << exponentWidth +1<< "))" << endl;
    smt2File << "(declare-fun bias_compare_overflow () (_ BitVec " << exponentWidth +1<< "))" << endl;
    // Der Bias-Wert für IEEE 754 (127 für 8-Bit Exponenten)
   if (length_max == 16) {
        smt2File << "(assert (= bias #b01111))" << endl; // 15
        smt2File << "(assert (= bias_inf_compare #b11111))" << endl; // 31
        smt2File << "(assert (= bias_extra #b001111))" << endl;
        smt2File << "(assert (= bias_compare_overflow #b101110))" << endl; // 46, 46 - 15 = 31 -> overflow
        smt2File << "(assert (= bias_compare_underflow #b001111))" << endl; // 15, 14 - 15 = -1 -> underflow
   } else if (length_max == 128) {
        smt2File << "(assert (= bias #b011111111111111))" << endl; // 16383
        smt2File << "(assert (= bias_inf_compare #b111111111111111))" << endl; // 32767
        smt2File << "(assert (= bias_extra #b0011111111111111))" << endl;
        smt2File << "(assert (= bias_compare_overflow #b1011111111111110))" << endl; // 49150, 49150 - 16383 = 32767 -> overflow
        smt2File << "(assert (= bias_compare_underflow #b0011111111111111))" << endl; // 16383, 16382 - 16383 = -1 -> underflow
   } else if (length_max == 32) {
        smt2File << "(assert (= bias #b01111111))" << endl; // 127
        smt2File << "(assert (= bias_inf_compare #b11111111))" << endl; // 255
        smt2File << "(assert (= bias_extra #b001111111))" << endl;
        smt2File << "(assert (= bias_compare_overflow #b101111110))" << endl; // 382, 382 - 127 = 255 -> overflow
        smt2File << "(assert (= bias_compare_underflow #b001111111))" << endl; // 127, 126 - 127 = -1 -> underflow
   } else if (length_max == 64) {
        smt2File << "(assert (= bias #b01111111111))" << endl; // 1023
        smt2File << "(assert (= bias_inf_compare #b11111111111))" << endl; // 2047
        smt2File << "(assert (= bias_extra #b001111111111))" << endl;
        smt2File << "(assert (= bias_compare_overflow #b101111111110))" << endl; // 3070, 3070 - 1023 = 2047 -> overflow
        smt2File << "(assert (= bias_compare_underflow #b001111111111))" << endl; // 1023, 1022 - 10237 = -1 -> underflow
   }

    smt2File << "(declare-fun g () (_ BitVec 1))" << endl;
    smt2File << "(declare-fun r () (_ BitVec 1))" << endl;
    smt2File << "(declare-fun s_help  () (_ BitVec "<< mantissaWidth - 2 <<"))" << endl;
    smt2File << "(declare-fun s_last () (_ BitVec 1))" << endl;
    smt2File << "(declare-fun s_outshift () (_ BitVec 1))" << endl;
    smt2File << "(declare-fun s  () (_ BitVec "<< mantissaWidth - 1 <<"))" << endl;

    smt2File << "(declare-fun lsb () (_ BitVec 1))" << endl;
/*
    string binary_x;
    string binary_y;

   if (length_max == 16) {
        binary_x = "0100000111000000";
        binary_y = "0100011110010111";
   } else if (length_max == 128) {
        binary_x = "01111111111111000011110000011111111111111111111111111111101000000000001111111111111111111111111111111111111111111111111110000011";
        binary_y = "00000000000111110001111111111111111111000000000000000000000000000011111111000000000000000000000000000011111110000000000000000000";
   } else if (length_max == 32) {
        binary_x = "01110001100000000000000000000000";
        binary_y = "01110011100111000000000000000111";
   } else if (length_max == 64) {
        binary_x = "0111111110000000000000001111111100000000000000000000000000000000";
        binary_y = "0100111110011100000000000011111111000000000000000000000000000111";
   }

   smt2File << "(assert (= x #b" << binary_x << "))" << endl;
   smt2File << "(assert (= y #b" << binary_y << "))" << endl;
*/
    smt2File << ";;; exract sign mantissa expo" << endl;

    smt2File << "(assert (= x_sign ((_ extract " << length_max - 1 << " " << length_max - 1 << ") x)))" << endl;
    smt2File << "(assert (= y_sign ((_ extract " << length_max - 1 << " " << length_max - 1 << ") y)))" << endl;

    smt2File << "(assert (= x_exponent ((_ extract " << length_max - 2 << " " << length_max - 1 - exponentWidth << ") x)))" << endl;
    smt2File << "(assert (= y_exponent ((_ extract " << length_max - 2 << " " << length_max - 1 - exponentWidth << ") y)))" << endl;

    smt2File << "(assert (= x_mantissa ((_ extract " << mantissaWidth - 1 << " 0) x)))" << endl;
    smt2File << "(assert (= y_mantissa ((_ extract " << length_max - 2 - exponentWidth << " 0) y)))" << endl;

    // Denormalized Numbers, which extend the mantissa without the extra bit.
    smt2File << "(assert (= x_mantissa_extra  (ite (= x_exponent comp_expo)(concat nullen_00 x_mantissa) (concat nullen_1 x_mantissa))))" << endl;
    smt2File << "(assert (= y_mantissa_extra  (ite (= y_exponent comp_expo)(concat nullen_00 y_mantissa) (concat nullen_1 y_mantissa))))" << endl;

    // Erweitern des Exponenten für Overflow
    smt2File << "(assert (= x_exponent_extra  (concat null x_exponent)))" << endl;
    smt2File << "(assert (= y_exponent_extra  (concat null y_exponent)))" << endl;
    smt2File << "(assert (= z_exponent_extra_help (bvadd x_exponent_extra y_exponent_extra)))" << endl;
    smt2File << "(assert (= z_exponent_extra(bvsub (bvadd x_exponent_extra y_exponent_extra) bias_extra)))" << endl;

    // Berechnung von z_sign als XOR von x_sign und y_sign
    smt2File << "(assert (= z_sign (bvxor x_sign y_sign)))" << endl;

   // Berechnung von z_exponent als Addition von x_exponent und y_exponent + Abzug der Bias (bfloat32 = 127)
    smt2File << "(assert (= z_exponent(bvsub (bvadd x_exponent y_exponent) bias)))" << endl;

    // Berechnung von z_mantissa als Multiplikation von x_mantissa und y_mantissa
    smt2File << "(assert (= z_mantissa_extra (bvmul x_mantissa_extra y_mantissa_extra)))" << endl;

    // Testen auf Normalisierung,ob der radix-point verschoben werden soll
    smt2File << "(declare-fun extra_bit () (_ BitVec 1))" << endl;
    smt2File << "(declare-fun extra_bit_2 () (_ BitVec 1))" << endl;
    smt2File << "(assert (= extra_bit (ite (or (= y_exponent comp_expo) (= x_exponent comp_expo)) eins ((_ extract "<<mant_length << " " << mant_length<<") z_mantissa_extra))))" << endl;
    smt2File << "(assert (= extra_bit_2 (ite (or (= y_exponent comp_expo) (= x_exponent comp_expo)) eins ((_ extract "<<mant_length + 1 << " " << mant_length + 1<<") z_mantissa_extra))))" << endl;
    //smt2File << "(assert (= extra_bit (ite (or (= y_exponent comp_expo) (= x_exponent comp_expo)) eins ((_ extract 2 2  ) z_mantissa_extra))))" << endl;
    //smt2File << "(assert (= extra_bit_2 (ite (or (= y_exponent comp_expo) (= x_exponent comp_expo)) eins ((_ extract 1 1) z_mantissa_extra))))" << endl;

    // Wenn nach links geshiftet wird die Exponente um 1 addiert
    smt2File << "(assert (= z_exponent_GRS (ite (and (or (and (= extra_bit_2 #b1)(= extra_bit #b1))(and (= extra_bit_2 #b1)(= extra_bit #b0)))(distinct z_exponent bias_inf_compare)) (bvadd z_exponent add_expo) z_exponent)))" << endl;

    //Denormalized Number, heißt es wird normal gerechnet wie immer, aber am ende ist die zahl dennoch denormalizied
    //smt2File<< "(assert (= z_exponent_deNorm (ite (or (= x_exponent comp_expo) (= y_exponent comp_expo)) comp_expo  z_exponent_GRS)))" << endl;

    // wenn einer der beiden Inputs 0 ist = soll es auhc null bleiben
   smt2File << "(assert (= z_exponent_zero (ite (or (and (= x_exponent comp_expo) (= x_mantissa_extra comp_mant )) (and (= y_exponent comp_expo) (= y_mantissa_extra comp_mant))) comp_expo z_exponent_GRS)))" << endl;

    // INF +  overflow Exponent
    smt2File << "(assert (= z_exponent_overflow (ite (or (= x_exponent comp_expo_1) (= y_exponent comp_expo_1)(= z_exponent_GRS comp_expo_1) (bvugt z_exponent_extra_help bias_compare_overflow)) comp_expo_1 z_exponent_zero)))" << endl;

    // Underflow
    smt2File << "(assert (= z_exponent_underflow (ite (bvugt bias_compare_underflow  z_exponent_extra_help ) comp_expo z_exponent_overflow)))" << endl;

    // Plan: ich habe das Minimum von #b1111 was
    // der Plan ist die Anzahl Nullen zu zählen indem ich #1111 - z_exponent_extra_help
    // falls z_exponent_extra_help kleiner ist.
    // Zählt die Anzahl Nullen nach dem radix Point
    smt2File << "(declare-fun count_underflow () (_ BitVec " << exponentWidth + 1<< "))" << endl;
    smt2File << "(assert (= count_underflow (ite (bvugt bias_compare_underflow  z_exponent_extra_help ) (bvsub bias_extra z_exponent_extra_help) (concat null comp_expo))))" << endl;

    // DH. Wenn EXPO = 0, dann solte erstmal einmalig nach rechts geshiftet werden.

    // Wir haben hier nur z_mantissa_extra
    // Overflow
    // Kontrollieren ob die Exponente zum Overflow wurde:
    smt2File << "(assert (= z_mantissa_overflow (ite (or (and (= x_exponent comp_expo_1)(= x_mantissa_extra comp_mant ))(and (= y_exponent comp_expo_1)(= y_mantissa_extra comp_mant))(= z_exponent_underflow comp_expo_1) (bvugt z_exponent_extra_help bias_compare_overflow)) comp_mant z_mantissa_extra)))" << endl;


    // Underflow
    // Dann wird geschaut ob die z_exponente ein denormalized Nummer ist: Wenn ja wird einmal nach rechts geshiftet sodass die erste zahl eine 0 ist
    smt2File << "(assert (= z_mantissa_underflow_0 (ite (= z_exponent_underflow comp_expo) (bvlshr z_mantissa_overflow shift_mant) z_mantissa_overflow)))" << endl;


    // Kontrollieren erstmla ob X oder Y eine 0 ist:
    //smt2File << "(assert (= z_mantissa_zero (ite (or (and (= x_exponent comp_expo) (= x_mantissa_extra comp_mant)) (and (= y_exponent comp_expo) (= y_mantissa_extra comp_mant))) comp_mant z_mantissa_extra)))" << endl;

    // Also falls hier die exponente 0 ist, dann soll das Ergebnis erstmal denormalisiert werden.
    // Danach kommt die Vorschleife, um wie viele Nullen wir nahc rehcts shiften müssen.
    smt2File << "(declare-fun shift_time_underflow_0 () (_ BitVec " << exponentWidth + 1<< "))" << endl;
    smt2File << "(assert (= shift_time_underflow_0  (_ bv0 " << exponentWidth + 1 << ")))" << endl;

    smt2File << "(declare-fun take_last_bit_0 () (_ BitVec 1 ))" << endl;
    smt2File << "(assert (= take_last_bit_0 ((_ extract 0 0 ) z_mantissa_overflow)))" << endl;


    for (int i = 1; i < mant_length  + 10; i++) {
             smt2File << "(declare-fun shift_time_underflow_"<<i<<" () (_ BitVec " << exponentWidth + 1<< "))" << endl;
             smt2File << "(declare-fun z_mantissa_underflow_"<<i<<" () (_ BitVec " <<mant_length + 2<< "))" << endl;
             smt2File << "(declare-fun take_last_bit_"<<i<<" () (_ BitVec 1 ))" << endl;
    }

    for(int x = 1; x < mant_length  + 10; x++){
        smt2File << "(assert (= shift_time_underflow_"<< x <<" (ite (and (= z_exponent_underflow comp_expo)(bvugt count_underflow shift_time_underflow_"<< x - 1 <<")) (bvadd shift_time_underflow_"<< x - 1 <<"  add_shift) shift_time_underflow_"<< x - 1 <<")))" << endl;
        smt2File << "(assert (= take_last_bit_"<<x<<" (ite  (and (= z_exponent_underflow comp_expo)(bvugt count_underflow shift_time_underflow_"<< x - 1 <<")) ((_ extract 0 0 ) z_mantissa_underflow_"<< x - 1 <<") null)))" << endl;
        smt2File << "(assert (= z_mantissa_underflow_"<< x <<" (ite  (and (= z_exponent_underflow comp_expo)(bvugt count_underflow shift_time_underflow_"<< x - 1 <<")) (bvlshr z_mantissa_underflow_"<< x - 1 <<" shift_mant) z_mantissa_underflow_"<< x - 1 <<")))" << endl;
    }

    //smt2File << "(declare-fun get_outshiftet_numbers  () (_ BitVec " <<mant_length + 2<< "))" << endl;

    smt2File << "(declare-fun add_outshift_number_0 () (_ BitVec 1))" << endl;
    smt2File << "(assert (= add_outshift_number_0 take_last_bit_0))" << endl;



    for(int x = 1; x < mant_length + 10; x++) {
        smt2File << "(declare-fun add_outshift_number_"<<x<<" () (_ BitVec 1))" << endl;
        smt2File << "(assert (= add_outshift_number_"<<x<<" (ite (or (= add_outshift_number_"<<x - 1<<" eins)(= take_last_bit_"<<x - 1<<" eins)) eins null)))" << endl;
            //smt2File << "(assert (= s_outshift (ite (= take_last_bit_"<<x<<" null) null eins)))" << endl;
    }

    // Nachdem wir geshiftet haben, müssen wir nun die Manitssa Größe anpassen und mit dem GRS runden
    smt2File << "(assert (= z_mantissa (ite (and (or (and (= extra_bit_2 #b1)(= extra_bit #b1))(and (= extra_bit_2 #b1)(= extra_bit #b0)))(distinct z_exponent_underflow comp_expo)) ((_ extract "<<mant_length<<" "<<mantissaWidth + 1<<") z_mantissa_underflow_"<<mant_length  + 9<<")(ite (and (or (and (= extra_bit_2 #b1)(= extra_bit #b1))(= extra_bit #b0))(= z_exponent_underflow comp_expo)) ((_ extract "<<mant_length - 1 <<" "<<mantissaWidth  <<") z_mantissa_underflow_"<<mant_length  + 9<<") ((_ extract "<<mant_length - 1<<" "<< mantissaWidth<<") z_mantissa_underflow_"<<mant_length  + 9<<")))))" << endl;

    smt2File << "(assert (= z_mantissa_rest (ite (and (or (and (= extra_bit_2 #b1)(= extra_bit #b1))(and (= extra_bit_2 #b1)(= extra_bit #b0)))(distinct z_exponent_underflow comp_expo)) ((_ extract "<<mantissaWidth<<" 1) z_mantissa_underflow_"<<mant_length  + 9<<")(ite (and (or (and (= extra_bit_2 #b1)(= extra_bit #b1))(= extra_bit #b0))(= z_exponent_underflow comp_expo)) ((_ extract "<<mantissaWidth - 1 <<" 0 ) z_mantissa_underflow_"<<mant_length  + 9<<") ((_ extract "<< mantissaWidth - 1<<" 0) z_mantissa_underflow_"<<mant_length  + 9<<")))))" << endl;

    // auf und abrunden der Mantissa
    // Aufrunden
    // Fall 1:
    // G = 1 ,Guard_bit = 1
    //Fall 2:
    //G = 1, R&S = 0 , Guard_bit = 1
    //
    // Abrunden:
    // Fall 1:
    // G = 0 , Guard_bit = 0
    // G = 1, R&S = 0 Guard_bit = 0

    // wenn nach links geshiftet, dann ändern sich die Positionen der GRS.
    smt2File << "(assert (= g (ite (and (or (and (= extra_bit_2 #b1)(= extra_bit #b1))(and (= extra_bit_2 #b1)(= extra_bit #b0)))(distinct z_exponent_underflow comp_expo)) ((_ extract "<<mantissaWidth<<" "<<mantissaWidth<<") z_mantissa_underflow_"<<mant_length  + 9<<")(ite (and (or (and (= extra_bit_2 #b1)(= extra_bit #b1))(= extra_bit #b0))(= z_exponent_underflow comp_expo)) ((_ extract "<<mantissaWidth - 1 <<" "<<mantissaWidth - 1 <<") z_mantissa_underflow_"<<mant_length  + 9<<") ((_ extract "<<mantissaWidth - 1<<" "<< mantissaWidth - 1 <<") z_mantissa_underflow_"<<mant_length  + 9<<")))))" << endl;

    smt2File << "(assert (= r (ite (and (or (and (= extra_bit_2 #b1)(= extra_bit #b1))(and (= extra_bit_2 #b1)(= extra_bit #b0)))(distinct z_exponent_underflow comp_expo)) ((_ extract "<<mantissaWidth - 1<<" "<<mantissaWidth - 1<<") z_mantissa_underflow_"<<mant_length  + 9<<")(ite (and (or (and (= extra_bit_2 #b1)(= extra_bit #b1))(= extra_bit #b0))(= z_exponent_underflow comp_expo)) ((_ extract "<<mantissaWidth - 2 <<" "<<mantissaWidth - 2 <<") z_mantissa_underflow_"<<mant_length  + 9<<") ((_ extract "<<mantissaWidth - 2<<" "<< mantissaWidth - 2 <<") z_mantissa_underflow_"<<mant_length  + 9<<")))))" << endl;

    smt2File << "(assert (= s_help (ite (and (or (and (= extra_bit_2 #b1)(= extra_bit #b1))(and (= extra_bit_2 #b1)(= extra_bit #b0)))(distinct z_exponent_underflow comp_expo)) ((_ extract "<<mantissaWidth-2<<" 1) z_mantissa_underflow_"<<mant_length  + 9<<")(ite (and (or (and (= extra_bit_2 #b1)(= extra_bit #b1))(= extra_bit #b0))(= z_exponent_underflow comp_expo)) ((_ extract "<<mantissaWidth - 3 <<" 0) z_mantissa_underflow_"<<mant_length  + 9<<") ((_ extract "<<mantissaWidth - 3<<" 0) z_mantissa_underflow_"<<mant_length  + 9<<")))))" << endl;

    smt2File << "(assert (= s_last (ite (and (or (and (= extra_bit_2 #b1)(= extra_bit #b1))(and (= extra_bit_2 #b1)(= extra_bit #b0)))(distinct z_exponent_underflow comp_expo)) ((_ extract 0 0) z_mantissa_underflow_"<<mant_length  + 9<<") null)))" << endl;

    smt2File << "(assert (= s (concat s_help s_last)))" << endl;
    // Zum Runden ist das Guard_bit wichtig, da es dazu dient dass es gerundet wird.
    smt2File << "(assert (= lsb (ite (and (or (and (= extra_bit_2 #b1)(= extra_bit #b1))(and (= extra_bit_2 #b1)(= extra_bit #b0)))(distinct z_exponent_underflow comp_expo)) ((_ extract "<<mantissaWidth + 1<<" "<<mantissaWidth + 1<<") z_mantissa_underflow_"<<mant_length  + 9<<")(ite (and (or (and (= extra_bit_2 #b1)(= extra_bit #b1))(= extra_bit #b0))(= z_exponent_underflow comp_expo)) ((_ extract "<<mantissaWidth  <<" "<<mantissaWidth  <<") z_mantissa_underflow_"<<mant_length  + 9<<") ((_ extract "<<mantissaWidth <<" "<< mantissaWidth<<") z_mantissa_underflow_"<<mant_length  + 9<<")))))" << endl;

    //0101
    //1100
    //1111
    //0111
    //1101
    //0101
    //1101

    //nur Aufrundfälle aufzählen, da beim abrunden, die z_mantisse nicht geändert wird sondern nur gecuttet
    smt2File << "(assert (= z_mantissa_GRS(ite (or (and (= g #b1) (or (= r #b1) (distinct s compare_s)(= add_outshift_number_"<<mant_length + 9 <<" eins))) (and (= g #b1) (= lsb #b1))) (bvadd z_mantissa add_mant) z_mantissa)))" << endl;

    smt2File << "(assert (= z_exponent_over (ite (and (= z_mantissa comp_mant_1) (= z_mantissa_GRS comp_mant_0)) (bvadd z_exponent_underflow add_expo)  z_exponent_underflow)))" << endl;


    smt2File << "(assert (= z_mantissa_NaN (ite (or (and (= x_exponent comp_expo_1) (distinct x_mantissa_extra comp_mant)) (and (= y_exponent comp_expo_1) (distinct y_mantissa_extra comp_mant))) comp_mant_1 z_mantissa_GRS)))" << endl;

    // concat everything and compare with fp
    smt2File << "(assert (= z (concat z_sign z_exponent_over )))" << endl;
    smt2File << "(assert (= z_finale (concat z z_mantissa_NaN)))" << endl;

    smt2File << "(check-sat)" << endl;
    smt2File << "(get-model)" << endl;


    smt2File << "(exit)" << endl;
    smt2File.close();

    cout << signWidth << endl;
    cout << exponentWidth << endl;
    cout << mantissaWidth << endl;
    cout << mant_length << endl;
    cout << length_max << endl;


    cout << "SMT2-Datei erfolgreich erstellt: BV"+sizebit+"_multiplication.smt2" << endl;
    return 0;
}

int bv_bv(string sizebit, int sign, int exponent,int mantissa) {

        fstream smt2File;
        smt2File.open("BV_BV_"+sizebit+"_multiplication.smt2",ios::out);
        smt2File << ";;; bfloat"+sizebit+" multiplication bv_bv" << endl;
        smt2File << "(set-option :produce-models true)" << endl;
        smt2File << "(set-logic QF_BV)" << endl; // Verwendung von QF_FPBV für Floating-Point Arithmetic
        smt2File << endl;
        smt2File << "(set-info :source |Benny Wennberg Bachelor thesis|)" << endl;        // ab hier Code

        // Schreiben von SMT2-Inhalten in die Datei

    // input variablen
    int signWidth = sign;
    int exponentWidth = exponent;
    int mantissaWidth = mantissa;
    int mant_length = mantissaWidth * 2;
    int length_max = stoi(sizebit);


    // Deklaration von festen Bit-Vektoren für Vorzeichen, Exponent und Mantisse für x, y und z
    smt2File <<  "(declare-fun eins () (_ BitVec " << signWidth << "))" << endl;
    smt2File << "(assert (= eins  #b1 ))" << endl;
    smt2File <<  "(declare-fun null () (_ BitVec " << signWidth << "))" << endl;
    smt2File << "(assert (= null  #b0 ))" << endl;

    smt2File <<  "(declare-fun compare_s () (_ BitVec " << mantissaWidth - 1<< "))" << endl;
    smt2File << "(assert (= compare_s  (_ bv0 " << mantissaWidth - 1<< ")))" << endl;

    smt2File << "(declare-fun comp_expo () (_ BitVec " << exponentWidth<<"))" << endl;
    smt2File << "(assert (= comp_expo  (_ bv0 " << exponentWidth << ")))" << endl;
    smt2File << "(declare-fun comp_mant () (_ BitVec " << mant_length + 2<<"))" << endl;
    smt2File << "(assert (= comp_mant  (_ bv0 " << mant_length + 2 << ")))" << endl;
    smt2File << "(declare-fun comp_mant_0 () (_ BitVec " << mantissaWidth<<"))" << endl;
    smt2File << "(assert (= comp_mant_0  (_ bv0 " << mantissaWidth << ")))" << endl;

    smt2File << "(declare-fun comp_expo_1 () (_ BitVec " << exponentWidth<<"))" << endl;
    smt2File << "(declare-fun comp_mant_1 () (_ BitVec " << mantissaWidth<<"))" << endl;
    if (length_max == 16) {
        smt2File << "(assert (= comp_mant_1 #b1111111111))" << endl;
        smt2File << "(assert (= comp_expo_1 #b11111))" << endl;
    } else if (length_max == 128) {
        smt2File << "(assert (= comp_mant_1 #b1111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111))" << endl;
        smt2File << "(assert (= comp_expo_1 #b111111111111111))" << std::endl;
    } else if (length_max == 32) {
         smt2File << "(assert (= comp_mant_1 #b11111111111111111111111))" << endl;
         smt2File << "(assert (= comp_expo_1 #b11111111))" << std::endl;
    } else if (length_max == 64) {
         smt2File << "(assert (= comp_mant_1 #b1111111111111111111111111111111111111111111111111111))" << endl;
         smt2File << "(assert (= comp_expo_1 #b11111111111))" << std::endl;
    }


    smt2File << "(declare-fun add_expo_0 () (_ BitVec " << exponentWidth - 1<<"))" << endl;
    smt2File << "(assert (= add_expo_0  (_ bv0 " << exponentWidth - 1 << ")))" << endl;
    smt2File << "(declare-fun add_expo () (_ BitVec " << exponentWidth <<"))" << endl;
    smt2File << "(assert (= add_expo (concat add_expo_0 eins)))" << endl;

    smt2File << "(declare-fun add_mant_0 () (_ BitVec " << mantissaWidth - 1<<"))" << endl;
    smt2File << "(assert (= add_mant_0  (_ bv0 " << mantissaWidth - 1 << ")))" << endl;
    smt2File << "(declare-fun add_mant () (_ BitVec " << mantissaWidth <<"))" << endl;
    smt2File << "(assert (= add_mant (concat add_mant_0 eins)))" << endl;


    smt2File << "(declare-fun add_shift_0 () (_ BitVec " << exponentWidth<<"))" << endl;
    smt2File << "(assert (= add_shift_0  (_ bv0 " << exponentWidth << ")))" << endl;
    smt2File << "(declare-fun add_shift () (_ BitVec " << exponentWidth + 1 <<"))" << endl;
    smt2File << "(assert (= add_shift (concat add_shift_0 eins)))" << endl;

    smt2File << "(declare-fun shift_mant_0 () (_ BitVec " << mant_length + 1<<"))" << endl;
    smt2File << "(assert (= shift_mant_0  (_ bv0 " << mant_length + 1 << ")))" << endl;
    smt2File << "(declare-fun shift_mant () (_ BitVec " << mant_length + 2<<"))" << endl;
    smt2File << "(assert (= shift_mant (concat shift_mant_0 eins)))" << endl;

    smt2File << "(declare-fun x () (_ BitVec " << length_max << "))" << endl;
    smt2File << "(declare-fun x_sign () (_ BitVec " << signWidth << "))" << endl;
    smt2File << "(declare-fun x_exponent () (_ BitVec " << exponentWidth << "))" << endl;
    smt2File << "(declare-fun x_mantissa () (_ BitVec " << mantissaWidth << "))" << endl;

    smt2File << "(declare-fun y () (_ BitVec " << length_max << "))" << endl;
    smt2File << "(declare-fun y_sign () (_ BitVec " << signWidth << "))" << endl;
    smt2File << "(declare-fun y_exponent () (_ BitVec " << exponentWidth << "))" << endl;
    smt2File << "(declare-fun y_mantissa () (_ BitVec " << mantissaWidth << "))" << endl;

        // extend Mantissa for multiplication
    smt2File << "(declare-fun x_exponent_extra () (_ BitVec " << exponentWidth + 1 << "))" << endl;
    smt2File << "(declare-fun y_exponent_extra () (_ BitVec " << exponentWidth + 1<< "))" << endl;
    smt2File << "(declare-fun z_exponent_extra_help () (_ BitVec " << exponentWidth + 1<< "))" << endl;
    smt2File << "(declare-fun z_exponent_extra () (_ BitVec " << exponentWidth + 1<< "))" << endl;

    // extend Mantissa for multiplication
    smt2File << "(declare-fun x_mantissa_extra () (_ BitVec " << mant_length + 2 << "))" << endl;
    smt2File << "(declare-fun y_mantissa_extra () (_ BitVec " << mant_length + 2<< "))" << endl;
    smt2File << "(declare-fun z_mantissa_extra () (_ BitVec " << mant_length + 2<< "))" << endl;


   // Get the extended Mantissa with beginning bit
    smt2File << "(declare-fun  nullen_0 () (_ BitVec " << mantissaWidth + 1 << "))" << endl;
    smt2File << "(assert (= nullen_0  (_ bv0 " << mantissaWidth + 1 << ")))" << endl;
    smt2File << "(declare-fun  nullen_1 () (_ BitVec " << mantissaWidth + 2 << "))" << endl;
    smt2File << "(assert (= nullen_1 (concat nullen_0 eins)))" << endl;

    smt2File << "(declare-fun  nullen_00 () (_ BitVec " << mantissaWidth + 2 << "))" << endl;
    smt2File << "(assert (= nullen_00 (_ bv0 " << mantissaWidth + 2 << ")))" << endl;

    // Z variablen
    smt2File << "(declare-fun z () (_ BitVec " << signWidth + exponentWidth << "))" << endl;
    smt2File << "(declare-fun z_finale () (_ BitVec " << length_max << "))" << endl;

    smt2File << "(declare-fun z_sign () (_ BitVec " << signWidth << "))" << endl;

    smt2File << "(declare-fun z_exponent () (_ BitVec " << exponentWidth << "))" << endl;
    smt2File << "(declare-fun z_exponent_GRS () (_ BitVec " << exponentWidth << "))" << endl;
    smt2File << "(declare-fun z_exponent_deNorm () (_ BitVec " << exponentWidth << "))" << endl;
    smt2File << "(declare-fun z_exponent_zero () (_ BitVec " << exponentWidth << "))" << endl;
    smt2File << "(declare-fun z_exponent_overflow () (_ BitVec " << exponentWidth << "))" << endl;
    smt2File << "(declare-fun z_exponent_underflow () (_ BitVec " << exponentWidth << "))" << endl;
    smt2File << "(declare-fun z_exponent_over () (_ BitVec " << exponentWidth << "))" << endl;

    smt2File << "(declare-fun z_mantissa () (_ BitVec " << mantissaWidth  << "))" << endl;
    smt2File << "(declare-fun z_mantissa_rest () (_ BitVec " << mantissaWidth  << "))" << endl;
    smt2File << "(declare-fun z_mantissa_GRS () (_ BitVec " << mantissaWidth  << "))" << endl;
    smt2File << "(declare-fun z_mantissa_zero () (_ BitVec " << mant_length + 2 << "))" << endl;
    smt2File << "(declare-fun z_mantissa_overflow () (_ BitVec " << mant_length + 2 << "))" << endl;
    smt2File << "(declare-fun z_mantissa_underflow_0 () (_ BitVec " << mant_length + 2 << "))" << endl;
    smt2File << "(declare-fun z_mantissa_NaN () (_ BitVec " << mantissaWidth << "))" << endl;


    // Addition hilfe Bias muss noch je nach Bitsize um (bei 32 bit um 127 abgezogen werden.)
    smt2File << "(declare-fun bias () (_ BitVec " << exponentWidth << "))" << endl;
    smt2File << "(declare-fun bias_inf_compare () (_ BitVec " << exponentWidth << "))" << endl;
    smt2File << "(declare-fun bias_extra () (_ BitVec " << exponentWidth +1<< "))" << endl;
    smt2File << "(declare-fun bias_compare_underflow () (_ BitVec " << exponentWidth +1<< "))" << endl;
    smt2File << "(declare-fun bias_compare_overflow () (_ BitVec " << exponentWidth +1<< "))" << endl;
    // Der Bias-Wert für IEEE 754 (127 für 8-Bit Exponenten)
   if (length_max == 16) {
        smt2File << "(assert (= bias #b01111))" << endl; // 15
        smt2File << "(assert (= bias_inf_compare #b11111))" << endl; // 31
        smt2File << "(assert (= bias_extra #b001111))" << endl;
        smt2File << "(assert (= bias_compare_overflow #b101110))" << endl; // 46, 46 - 15 = 31 -> overflow
        smt2File << "(assert (= bias_compare_underflow #b001111))" << endl; // 15, 14 - 15 = -1 -> underflow
   } else if (length_max == 128) {
        smt2File << "(assert (= bias #b011111111111111))" << endl; // 16383
        smt2File << "(assert (= bias_inf_compare #b111111111111111))" << endl; // 32767
        smt2File << "(assert (= bias_extra #b0011111111111111))" << endl;
        smt2File << "(assert (= bias_compare_overflow #b1011111111111110))" << endl; // 49150, 49150 - 16383 = 32767 -> overflow
        smt2File << "(assert (= bias_compare_underflow #b0011111111111111))" << endl; // 16383, 16382 - 16383 = -1 -> underflow
   } else if (length_max == 32) {
        smt2File << "(assert (= bias #b01111111))" << endl; // 127
        smt2File << "(assert (= bias_inf_compare #b11111111))" << endl; // 255
        smt2File << "(assert (= bias_extra #b001111111))" << endl;
        smt2File << "(assert (= bias_compare_overflow #b101111110))" << endl; // 382, 382 - 127 = 255 -> overflow
        smt2File << "(assert (= bias_compare_underflow #b001111111))" << endl; // 127, 126 - 127 = -1 -> underflow
   } else if (length_max == 64) {
        smt2File << "(assert (= bias #b01111111111))" << endl; // 1023
        smt2File << "(assert (= bias_inf_compare #b11111111111))" << endl; // 2047
        smt2File << "(assert (= bias_extra #b001111111111))" << endl;
        smt2File << "(assert (= bias_compare_overflow #b101111111110))" << endl; // 3070, 3070 - 1023 = 2047 -> overflow
        smt2File << "(assert (= bias_compare_underflow #b001111111111))" << endl; // 1023, 1022 - 10237 = -1 -> underflow
   }

    smt2File << "(declare-fun g () (_ BitVec 1))" << endl;
    smt2File << "(declare-fun r () (_ BitVec 1))" << endl;
    smt2File << "(declare-fun s_help  () (_ BitVec "<< mantissaWidth - 2 <<"))" << endl;
    smt2File << "(declare-fun s_last () (_ BitVec 1))" << endl;
    smt2File << "(declare-fun s_outshift () (_ BitVec 1))" << endl;
    smt2File << "(declare-fun s  () (_ BitVec "<< mantissaWidth - 1 <<"))" << endl;

    smt2File << "(declare-fun lsb () (_ BitVec 1))" << endl;
    
/*
    string binary_x;
    string binary_y;

   if (length_max == 16) {
        binary_x = "0100000111000000";
        binary_y = "0100011110010111";
   } else if (length_max == 128) {
        binary_x = "01111111111111000011110000011111111111111111111111111111101000000000001111111111111111111111111111111111111111111111111110000011";
        binary_y = "00000000000111110001111111111111111111000000000000000000000000000011111111000000000000000000000000000011111110000000000000000000";
   } else if (length_max == 32) {
        binary_x = "01110001100000000000000000000000";
        binary_y = "01110011100111000000000000000111";
   } else if (length_max == 64) {
        binary_x = "0111111110000000000000001111111100000000000000000000000000000000";
        binary_y = "0100111110011100000000000011111111000000000000000000000000000111";
   }

   smt2File << "(assert (= x #b" << binary_x << "))" << endl;
    smt2File << "(assert (= y #b" << binary_y << "))" << endl;
  */
    // exract sign, expo and mant
    // Vorzeichen extrahieren
    smt2File << ";;; exract sign mantissa expo" << endl;

    smt2File << "(assert (= x_sign ((_ extract " << length_max - 1 << " " << length_max - 1 << ") x)))" << endl;
    smt2File << "(assert (= y_sign ((_ extract " << length_max - 1 << " " << length_max - 1 << ") y)))" << endl;

    smt2File << "(assert (= x_exponent ((_ extract " << length_max - 2 << " " << length_max - 1 - exponentWidth << ") x)))" << endl;
    smt2File << "(assert (= y_exponent ((_ extract " << length_max - 2 << " " << length_max - 1 - exponentWidth << ") y)))" << endl;

    smt2File << "(assert (= x_mantissa ((_ extract " << mantissaWidth - 1 << " 0) x)))" << endl;
    smt2File << "(assert (= y_mantissa ((_ extract " << length_max - 2 - exponentWidth << " 0) y)))" << endl;

    // Denormalized Numbers, which extend the mantissa without the extra bit.
    smt2File << "(assert (= x_mantissa_extra  (ite (= x_exponent comp_expo)(concat nullen_00 x_mantissa) (concat nullen_1 x_mantissa))))" << endl;
    smt2File << "(assert (= y_mantissa_extra  (ite (= y_exponent comp_expo)(concat nullen_00 y_mantissa) (concat nullen_1 y_mantissa))))" << endl;

    // Erweitern des Exponenten für Overflow
    smt2File << "(assert (= x_exponent_extra  (concat null x_exponent)))" << endl;
    smt2File << "(assert (= y_exponent_extra  (concat null y_exponent)))" << endl;
    smt2File << "(assert (= z_exponent_extra_help (bvadd x_exponent_extra y_exponent_extra)))" << endl;
    smt2File << "(assert (= z_exponent_extra(bvsub (bvadd x_exponent_extra y_exponent_extra) bias_extra)))" << endl;

    // Berechnung von z_sign als XOR von x_sign und y_sign
    smt2File << "(assert (= z_sign (bvxor x_sign y_sign)))" << endl;

   // Berechnung von z_exponent als Addition von x_exponent und y_exponent + Abzug der Bias (bfloat32 = 127)
    smt2File << "(assert (= z_exponent(bvsub (bvadd x_exponent y_exponent) bias)))" << endl;

    // Berechnung von z_mantissa als Multiplikation von x_mantissa und y_mantissa
    smt2File << "(assert (= z_mantissa_extra (bvmul x_mantissa_extra y_mantissa_extra)))" << endl;

    // Testen auf Normalisierung,ob der radix-point verschoben werden soll
    smt2File << "(declare-fun extra_bit () (_ BitVec 1))" << endl;
    smt2File << "(declare-fun extra_bit_2 () (_ BitVec 1))" << endl;
    smt2File << "(assert (= extra_bit (ite (or (= y_exponent comp_expo) (= x_exponent comp_expo)) eins ((_ extract "<<mant_length << " " << mant_length<<") z_mantissa_extra))))" << endl;
    smt2File << "(assert (= extra_bit_2 (ite (or (= y_exponent comp_expo) (= x_exponent comp_expo)) eins ((_ extract "<<mant_length + 1 << " " << mant_length + 1<<") z_mantissa_extra))))" << endl;
    //smt2File << "(assert (= extra_bit (ite (or (= y_exponent comp_expo) (= x_exponent comp_expo)) eins ((_ extract 2 2  ) z_mantissa_extra))))" << endl;
    //smt2File << "(assert (= extra_bit_2 (ite (or (= y_exponent comp_expo) (= x_exponent comp_expo)) eins ((_ extract 1 1) z_mantissa_extra))))" << endl;

    // Wenn nach links geshiftet wird die Exponente um 1 addiert
    smt2File << "(assert (= z_exponent_GRS (ite (and (or (and (= extra_bit_2 #b1)(= extra_bit #b1))(and (= extra_bit_2 #b1)(= extra_bit #b0)))(distinct z_exponent bias_inf_compare)) (bvadd z_exponent add_expo) z_exponent)))" << endl;

    //Denormalized Number, heißt es wird normal gerechnet wie immer, aber am ende ist die zahl dennoch denormalizied
    //smt2File<< "(assert (= z_exponent_deNorm (ite (or (= x_exponent comp_expo) (= y_exponent comp_expo)) comp_expo  z_exponent_GRS)))" << endl;

    // wenn einer der beiden Inputs 0 ist = soll es auhc null bleiben
   smt2File << "(assert (= z_exponent_zero (ite (or (and (= x_exponent comp_expo) (= x_mantissa_extra comp_mant )) (and (= y_exponent comp_expo) (= y_mantissa_extra comp_mant))) comp_expo z_exponent_GRS)))" << endl;

    // INF +  overflow Exponent
    smt2File << "(assert (= z_exponent_overflow (ite (or (= x_exponent comp_expo_1) (= y_exponent comp_expo_1)(= z_exponent_GRS comp_expo_1) (bvugt z_exponent_extra_help bias_compare_overflow)) comp_expo_1 z_exponent_zero)))" << endl;

    // Underflow
    smt2File << "(assert (= z_exponent_underflow (ite (bvugt bias_compare_underflow  z_exponent_extra_help ) comp_expo z_exponent_overflow)))" << endl;

    // Plan: ich habe das Minimum von #b1111 was
    // der Plan ist die Anzahl Nullen zu zählen indem ich #1111 - z_exponent_extra_help
    // falls z_exponent_extra_help kleiner ist.
    // Zählt die Anzahl Nullen nach dem radix Point
    smt2File << "(declare-fun count_underflow () (_ BitVec " << exponentWidth + 1<< "))" << endl;
    smt2File << "(assert (= count_underflow (ite (bvugt bias_compare_underflow  z_exponent_extra_help ) (bvsub bias_extra z_exponent_extra_help) (concat null comp_expo))))" << endl;

    // DH. Wenn EXPO = 0, dann solte erstmal einmalig nach rechts geshiftet werden.

    // Wir haben hier nur z_mantissa_extra
    // Overflow
    // Kontrollieren ob die Exponente zum Overflow wurde:
    smt2File << "(assert (= z_mantissa_overflow (ite (or (and (= x_exponent comp_expo_1)(= x_mantissa_extra comp_mant ))(and (= y_exponent comp_expo_1)(= y_mantissa_extra comp_mant))(= z_exponent_underflow comp_expo_1) (bvugt z_exponent_extra_help bias_compare_overflow)) comp_mant z_mantissa_extra)))" << endl;


    // Underflow
    // Dann wird geschaut ob die z_exponente ein denormalized Nummer ist: Wenn ja wird einmal nach rechts geshiftet sodass die erste zahl eine 0 ist
    smt2File << "(assert (= z_mantissa_underflow_0 (ite (= z_exponent_underflow comp_expo) (bvlshr z_mantissa_overflow shift_mant) z_mantissa_overflow)))" << endl;


    // Kontrollieren erstmla ob X oder Y eine 0 ist:
    //smt2File << "(assert (= z_mantissa_zero (ite (or (and (= x_exponent comp_expo) (= x_mantissa_extra comp_mant)) (and (= y_exponent comp_expo) (= y_mantissa_extra comp_mant))) comp_mant z_mantissa_extra)))" << endl;

    // Also falls hier die exponente 0 ist, dann soll das Ergebnis erstmal denormalisiert werden.
    // Danach kommt die Vorschleife, um wie viele Nullen wir nahc rehcts shiften müssen.
    smt2File << "(declare-fun shift_time_underflow_0 () (_ BitVec " << exponentWidth + 1<< "))" << endl;
    smt2File << "(assert (= shift_time_underflow_0  (_ bv0 " << exponentWidth + 1 << ")))" << endl;

    smt2File << "(declare-fun take_last_bit_0 () (_ BitVec 1 ))" << endl;
    smt2File << "(assert (= take_last_bit_0 ((_ extract 0 0 ) z_mantissa_overflow)))" << endl;


    for (int i = 1; i < mant_length  + 10; i++) {
             smt2File << "(declare-fun shift_time_underflow_"<<i<<" () (_ BitVec " << exponentWidth + 1<< "))" << endl;
             smt2File << "(declare-fun z_mantissa_underflow_"<<i<<" () (_ BitVec " <<mant_length + 2<< "))" << endl;
             smt2File << "(declare-fun take_last_bit_"<<i<<" () (_ BitVec 1 ))" << endl;
    }

    for(int x = 1; x < mant_length  + 10; x++){
        smt2File << "(assert (= shift_time_underflow_"<< x <<" (ite (and (= z_exponent_underflow comp_expo)(bvugt count_underflow shift_time_underflow_"<< x - 1 <<")) (bvadd shift_time_underflow_"<< x - 1 <<"  add_shift) shift_time_underflow_"<< x - 1 <<")))" << endl;
        smt2File << "(assert (= take_last_bit_"<<x<<" (ite  (and (= z_exponent_underflow comp_expo)(bvugt count_underflow shift_time_underflow_"<< x - 1 <<")) ((_ extract 0 0 ) z_mantissa_underflow_"<< x - 1 <<") null)))" << endl;
        smt2File << "(assert (= z_mantissa_underflow_"<< x <<" (ite  (and (= z_exponent_underflow comp_expo)(bvugt count_underflow shift_time_underflow_"<< x - 1 <<")) (bvlshr z_mantissa_underflow_"<< x - 1 <<" shift_mant) z_mantissa_underflow_"<< x - 1 <<")))" << endl;
    }

    //smt2File << "(declare-fun get_outshiftet_numbers  () (_ BitVec " <<mant_length + 2<< "))" << endl;

    smt2File << "(declare-fun add_outshift_number_0 () (_ BitVec 1))" << endl;
    smt2File << "(assert (= add_outshift_number_0 take_last_bit_0))" << endl;



    for(int x = 1; x < mant_length + 10; x++) {
        smt2File << "(declare-fun add_outshift_number_"<<x<<" () (_ BitVec 1))" << endl;
        smt2File << "(assert (= add_outshift_number_"<<x<<" (ite (or (= add_outshift_number_"<<x - 1<<" eins)(= take_last_bit_"<<x - 1<<" eins)) eins null)))" << endl;
            //smt2File << "(assert (= s_outshift (ite (= take_last_bit_"<<x<<" null) null eins)))" << endl;
    }

    // Nachdem wir geshiftet haben, müssen wir nun die Manitssa Größe anpassen und mit dem GRS runden
    smt2File << "(assert (= z_mantissa (ite (and (or (and (= extra_bit_2 #b1)(= extra_bit #b1))(and (= extra_bit_2 #b1)(= extra_bit #b0)))(distinct z_exponent_underflow comp_expo)) ((_ extract "<<mant_length<<" "<<mantissaWidth + 1<<") z_mantissa_underflow_"<<mant_length  + 9<<")(ite (and (or (and (= extra_bit_2 #b1)(= extra_bit #b1))(= extra_bit #b0))(= z_exponent_underflow comp_expo)) ((_ extract "<<mant_length - 1 <<" "<<mantissaWidth  <<") z_mantissa_underflow_"<<mant_length  + 9<<") ((_ extract "<<mant_length - 1<<" "<< mantissaWidth<<") z_mantissa_underflow_"<<mant_length  + 9<<")))))" << endl;

    smt2File << "(assert (= z_mantissa_rest (ite (and (or (and (= extra_bit_2 #b1)(= extra_bit #b1))(and (= extra_bit_2 #b1)(= extra_bit #b0)))(distinct z_exponent_underflow comp_expo)) ((_ extract "<<mantissaWidth<<" 1) z_mantissa_underflow_"<<mant_length  + 9<<")(ite (and (or (and (= extra_bit_2 #b1)(= extra_bit #b1))(= extra_bit #b0))(= z_exponent_underflow comp_expo)) ((_ extract "<<mantissaWidth - 1 <<" 0 ) z_mantissa_underflow_"<<mant_length  + 9<<") ((_ extract "<< mantissaWidth - 1<<" 0) z_mantissa_underflow_"<<mant_length  + 9<<")))))" << endl;

   // auf und abrunden der Mantissa
    // Aufrunden
    // Fall 1:
    // G = 1 ,Guard_bit = 1
    //Fall 2:
    //G = 1, R&S = 0 , Guard_bit = 1
    //
    // Abrunden:
    // Fall 1:
    // G = 0 , Guard_bit = 0
    // G = 1, R&S = 0 Guard_bit = 0

    // wenn nach links geshiftet, dann ändern sich die Positionen der GRS.
    smt2File << "(assert (= g (ite (and (or (and (= extra_bit_2 #b1)(= extra_bit #b1))(and (= extra_bit_2 #b1)(= extra_bit #b0)))(distinct z_exponent_underflow comp_expo)) ((_ extract "<<mantissaWidth<<" "<<mantissaWidth<<") z_mantissa_underflow_"<<mant_length  + 9<<")(ite (and (or (and (= extra_bit_2 #b1)(= extra_bit #b1))(= extra_bit #b0))(= z_exponent_underflow comp_expo)) ((_ extract "<<mantissaWidth - 1 <<" "<<mantissaWidth - 1 <<") z_mantissa_underflow_"<<mant_length  + 9<<") ((_ extract "<<mantissaWidth - 1<<" "<< mantissaWidth - 1 <<") z_mantissa_underflow_"<<mant_length  + 9<<")))))" << endl;

    smt2File << "(assert (= r (ite (and (or (and (= extra_bit_2 #b1)(= extra_bit #b1))(and (= extra_bit_2 #b1)(= extra_bit #b0)))(distinct z_exponent_underflow comp_expo)) ((_ extract "<<mantissaWidth - 1<<" "<<mantissaWidth - 1<<") z_mantissa_underflow_"<<mant_length  + 9<<")(ite (and (or (and (= extra_bit_2 #b1)(= extra_bit #b1))(= extra_bit #b0))(= z_exponent_underflow comp_expo)) ((_ extract "<<mantissaWidth - 2 <<" "<<mantissaWidth - 2 <<") z_mantissa_underflow_"<<mant_length  + 9<<") ((_ extract "<<mantissaWidth - 2<<" "<< mantissaWidth - 2 <<") z_mantissa_underflow_"<<mant_length  + 9<<")))))" << endl;

    smt2File << "(assert (= s_help (ite (and (or (and (= extra_bit_2 #b1)(= extra_bit #b1))(and (= extra_bit_2 #b1)(= extra_bit #b0)))(distinct z_exponent_underflow comp_expo)) ((_ extract "<<mantissaWidth-2<<" 1) z_mantissa_underflow_"<<mant_length  + 9<<")(ite (and (or (and (= extra_bit_2 #b1)(= extra_bit #b1))(= extra_bit #b0))(= z_exponent_underflow comp_expo)) ((_ extract "<<mantissaWidth - 3 <<" 0) z_mantissa_underflow_"<<mant_length  + 9<<") ((_ extract "<<mantissaWidth - 3<<" 0) z_mantissa_underflow_"<<mant_length  + 9<<")))))" << endl;

    smt2File << "(assert (= s_last (ite (and (or (and (= extra_bit_2 #b1)(= extra_bit #b1))(and (= extra_bit_2 #b1)(= extra_bit #b0)))(distinct z_exponent_underflow comp_expo)) ((_ extract 0 0) z_mantissa_underflow_"<<mant_length  + 9<<") null)))" << endl;

    smt2File << "(assert (= s (concat s_help s_last)))" << endl;
    // Zum Runden ist das Guard_bit wichtig, da es dazu dient dass es gerundet wird.
    smt2File << "(assert (= lsb (ite (and (or (and (= extra_bit_2 #b1)(= extra_bit #b1))(and (= extra_bit_2 #b1)(= extra_bit #b0)))(distinct z_exponent_underflow comp_expo)) ((_ extract "<<mantissaWidth + 1<<" "<<mantissaWidth + 1<<") z_mantissa_underflow_"<<mant_length  + 9<<")(ite (and (or (and (= extra_bit_2 #b1)(= extra_bit #b1))(= extra_bit #b0))(= z_exponent_underflow comp_expo)) ((_ extract "<<mantissaWidth  <<" "<<mantissaWidth  <<") z_mantissa_underflow_"<<mant_length  + 9<<") ((_ extract "<<mantissaWidth <<" "<< mantissaWidth<<") z_mantissa_underflow_"<<mant_length  + 9<<")))))" << endl;

    //0101
    //1100
    //1111
    //0111
    //1101
    //0101
    //1101

    //nur Aufrundfälle aufzählen, da beim abrunden, die z_mantisse nicht geändert wird sondern nur gecuttet
    smt2File << "(assert (= z_mantissa_GRS(ite (or (and (= g #b1) (or (= r #b1) (distinct s compare_s)(= add_outshift_number_"<<mant_length + 9 <<" eins))) (and (= g #b1) (= lsb #b1))) (bvadd z_mantissa add_mant) z_mantissa)))" << endl;

    smt2File << "(assert (= z_exponent_over (ite (and (= z_mantissa comp_mant_1) (= z_mantissa_GRS comp_mant_0)) (bvadd z_exponent_underflow add_expo)  z_exponent_underflow)))" << endl;


    smt2File << "(assert (= z_mantissa_NaN (ite (or (and (= x_exponent comp_expo_1) (distinct x_mantissa_extra comp_mant)) (and (= y_exponent comp_expo_1) (distinct y_mantissa_extra comp_mant))) comp_mant_1 z_mantissa_GRS)))" << endl;

    // concat everything and compare with fp
    smt2File << "(assert (= z (concat z_sign z_exponent_over )))" << endl;
    smt2File << "(assert (= z_finale (concat z z_mantissa_NaN)))" << endl;


    // ----------------------------------------------------------------------------------
    // ----------------------------------------------------------------------------------
    // ----------------------------------------------------------------------------------
    // duplicate Code

    smt2File << "(declare-fun a () (_ BitVec " << length_max << "))" << endl;
    smt2File << "(declare-fun a_sign () (_ BitVec " << signWidth << "))" << endl;
    smt2File << "(declare-fun a_exponent () (_ BitVec " << exponentWidth << "))" << endl;
    smt2File << "(declare-fun a_mantissa () (_ BitVec " << mantissaWidth << "))" << endl;

    smt2File << "(declare-fun b () (_ BitVec " << length_max << "))" << endl;
    smt2File << "(declare-fun b_sign () (_ BitVec " << signWidth << "))" << endl;
    smt2File << "(declare-fun b_exponent () (_ BitVec " << exponentWidth << "))" << endl;
    smt2File << "(declare-fun b_mantissa () (_ BitVec " << mantissaWidth << "))" << endl;

        // extend Mantissa for multiplication
    smt2File << "(declare-fun a_exponent_extra () (_ BitVec " << exponentWidth + 1 << "))" << endl;
    smt2File << "(declare-fun b_exponent_extra () (_ BitVec " << exponentWidth + 1<< "))" << endl;
    smt2File << "(declare-fun c_exponent_extra_help () (_ BitVec " << exponentWidth + 1<< "))" << endl;
    smt2File << "(declare-fun c_exponent_extra () (_ BitVec " << exponentWidth + 1<< "))" << endl;

    // extend Mantissa for multiplication
    smt2File << "(declare-fun a_mantissa_extra () (_ BitVec " << mant_length + 2 << "))" << endl;
    smt2File << "(declare-fun b_mantissa_extra () (_ BitVec " << mant_length + 2<< "))" << endl;
    smt2File << "(declare-fun c_mantissa_extra () (_ BitVec " << mant_length + 2<< "))" << endl;

    // c variablen
    smt2File << "(declare-fun c () (_ BitVec " << signWidth + exponentWidth << "))" << endl;
    smt2File << "(declare-fun c_finale () (_ BitVec " << length_max << "))" << endl;

    smt2File << "(declare-fun c_sign () (_ BitVec " << signWidth << "))" << endl;

    smt2File << "(declare-fun c_exponent () (_ BitVec " << exponentWidth << "))" << endl;
    smt2File << "(declare-fun c_exponent_GRS () (_ BitVec " << exponentWidth << "))" << endl;
    smt2File << "(declare-fun c_exponent_deNorm () (_ BitVec " << exponentWidth << "))" << endl;
    smt2File << "(declare-fun c_exponent_zero () (_ BitVec " << exponentWidth << "))" << endl;
    smt2File << "(declare-fun c_exponent_overflow () (_ BitVec " << exponentWidth << "))" << endl;
    smt2File << "(declare-fun c_exponent_underflow () (_ BitVec " << exponentWidth << "))" << endl;
    smt2File << "(declare-fun c_exponent_over_() (_ BitVec " << exponentWidth << "))" << endl;

    smt2File << "(declare-fun c_mantissa () (_ BitVec " << mantissaWidth  << "))" << endl;
    smt2File << "(declare-fun c_mantissa_rest () (_ BitVec " << mantissaWidth  << "))" << endl;
    smt2File << "(declare-fun c_mantissa_GRS () (_ BitVec " << mantissaWidth  << "))" << endl;
    smt2File << "(declare-fun c_mantissa_zero () (_ BitVec " << mant_length + 2 << "))" << endl;
    smt2File << "(declare-fun c_mantissa_overflow () (_ BitVec " << mant_length + 2 << "))" << endl;
    smt2File << "(declare-fun c_mantissa_underflow_0 () (_ BitVec " << mant_length + 2 << "))" << endl;
    smt2File << "(declare-fun c_mantissa_NaN () (_ BitVec " << mantissaWidth << "))" << endl;

    smt2File << "(declare-fun g_ () (_ BitVec 1))" << endl;
    smt2File << "(declare-fun r_() (_ BitVec 1))" << endl;
    smt2File << "(declare-fun s_help_  () (_ BitVec "<< mantissaWidth - 2 <<"))" << endl;
    smt2File << "(declare-fun s_last_ () (_ BitVec 1))" << endl;
    smt2File << "(declare-fun s_outshift_ () (_ BitVec 1))" << endl;
    smt2File << "(declare-fun s_  () (_ BitVec "<< mantissaWidth - 1 <<"))" << endl;

    smt2File << "(declare-fun lsb_ () (_ BitVec 1))" << endl;

    // exract sign, expo and mant
    // Vorzeichen extrahieren
    smt2File << ";;; exract sign mantissa expo" << endl;

    smt2File << "(assert (= a_sign ((_ extract " << length_max - 1 << " " << length_max - 1 << ") a)))" << endl;
    smt2File << "(assert (= b_sign ((_ extract " << length_max - 1 << " " << length_max - 1 << ") b)))" << endl;

    smt2File << "(assert (= a_exponent ((_ extract " << length_max - 2 << " " << length_max - 1 - exponentWidth << ") a)))" << endl;
    smt2File << "(assert (= b_exponent ((_ extract " << length_max - 2 << " " << length_max - 1 - exponentWidth << ") b)))" << endl;

    smt2File << "(assert (= a_mantissa ((_ extract " << mantissaWidth - 1 << " 0) a)))" << endl;
    smt2File << "(assert (= b_mantissa ((_ extract " << length_max - 2 - exponentWidth << " 0) b)))" << endl;

    // Denormalized Numbers, which extend the mantissa without the extra bit.
    smt2File << "(assert (= a_mantissa_extra  (ite (= a_exponent comp_expo)(concat nullen_00 a_mantissa) (concat nullen_1 a_mantissa))))" << endl;
    smt2File << "(assert (= b_mantissa_extra  (ite (= b_exponent comp_expo)(concat nullen_00 b_mantissa) (concat nullen_1 b_mantissa))))" << endl;

    // Erweitern des Exponenten für Overflow
    smt2File << "(assert (= a_exponent_extra  (concat null a_exponent)))" << endl;
    smt2File << "(assert (= b_exponent_extra  (concat null b_exponent)))" << endl;
    smt2File << "(assert (= c_exponent_extra_help (bvadd a_exponent_extra b_exponent_extra)))" << endl;
    smt2File << "(assert (= c_exponent_extra(bvsub (bvadd a_exponent_extra b_exponent_extra) bias_extra)))" << endl;

    // Berechnung von c_sign als XOR von a_sign und b_sign
    smt2File << "(assert (= c_sign (bvxor a_sign b_sign)))" << endl;

   // Berechnung von c_exponent als Addition von a_exponent und b_exponent + Abzug der Bias (bfloat32 = 127)
    smt2File << "(assert (= c_exponent(bvsub (bvadd a_exponent b_exponent) bias)))" << endl;

    // Berechnung von c_mantissa als Multiplikation von a_mantissa und b_mantissa
    smt2File << "(assert (= c_mantissa_extra (bvmul a_mantissa_extra b_mantissa_extra)))" << endl;

    // Testen auf Normalisierung,ob der radix-point verschoben werden soll
    smt2File << "(declare-fun extra_bit_c () (_ BitVec 1))" << endl;
    smt2File << "(declare-fun extra_bit_c_2 () (_ BitVec 1))" << endl;
    smt2File << "(assert (= extra_bit_c (ite (or (= b_exponent comp_expo) (= a_exponent comp_expo)) eins ((_ extract "<<mant_length << " " << mant_length<<") c_mantissa_extra))))" << endl;
    smt2File << "(assert (= extra_bit_c_2 (ite (or (= b_exponent comp_expo) (= a_exponent comp_expo)) eins ((_ extract "<<mant_length + 1 << " " << mant_length + 1<<") c_mantissa_extra))))" << endl;
    //smt2File << "(assert (= extra_bit_c (ite (or (= b_exponent comp_expo) (= a_exponent comp_expo)) eins ((_ extract 2 2  ) c_mantissa_extra))))" << endl;
    //smt2File << "(assert (= extra_bit_c_2 (ite (or (= b_exponent comp_expo) (= a_exponent comp_expo)) eins ((_ extract 1 1) c_mantissa_extra))))" << endl;

    // Wenn nach links geshiftet wird die Exponente um 1 addiert
    smt2File << "(assert (= c_exponent_GRS (ite (and (or (and (= extra_bit_c_2 #b1)(= extra_bit_c #b1))(and (= extra_bit_c_2 #b1)(= extra_bit_c #b0)))(distinct c_exponent bias_inf_compare)) (bvadd c_exponent add_expo) c_exponent)))" << endl;


    // wenn einer der beiden Inputs 0 ist = soll es auhc null bleiben
   smt2File << "(assert (= c_exponent_zero (ite (or (and (= a_exponent comp_expo) (= a_mantissa_extra comp_mant )) (and (= b_exponent comp_expo) (= b_mantissa_extra comp_mant))) comp_expo c_exponent_GRS)))" << endl;

    // INF +  overflow Exponent
    smt2File << "(assert (= c_exponent_overflow (ite (or (= a_exponent comp_expo_1) (= b_exponent comp_expo_1)(= c_exponent_GRS comp_expo_1) (bvugt c_exponent_extra_help bias_compare_overflow)) comp_expo_1 c_exponent_zero)))" << endl;

    // Underflow
    smt2File << "(assert (= c_exponent_underflow (ite (bvugt bias_compare_underflow  c_exponent_extra_help ) comp_expo c_exponent_overflow)))" << endl;

    // Plan: ich habe das Minimum von #b1111 was
    // der Plan ist die Anzahl Nullen zu zählen indem ich #1111 - c_exponent_extra_help
    // falls c_exponent_extra_help kleiner ist.
    // Zählt die Anzahl Nullen nach dem radix Point
    smt2File << "(declare-fun count_underflow_c () (_ BitVec " << exponentWidth + 1<< "))" << endl;
    smt2File << "(assert (= count_underflow_c (ite (bvugt bias_compare_underflow  c_exponent_extra_help ) (bvsub bias_extra c_exponent_extra_help) (concat null comp_expo))))" << endl;

    // DH. Wenn EXPO = 0, dann solte erstmal einmalig nach rechts geshiftet werden.

    // Wir haben hier nur c_mantissa_extra
    // Overflow
    // Kontrollieren ob die Exponente zum Overflow wurde:
    smt2File << "(assert (= c_mantissa_overflow (ite (or (and (= a_exponent comp_expo_1)(= a_mantissa_extra comp_mant ))(and (= b_exponent comp_expo_1)(= b_mantissa_extra comp_mant))(= c_exponent_underflow comp_expo_1) (bvugt c_exponent_extra_help bias_compare_overflow)) comp_mant c_mantissa_extra)))" << endl;

    //

    // Underflow
    // Dann wird geschaut ob die c_exponente ein denormalized Nummer ist: Wenn ja wird einmal nach rechts geshiftet sodass die erste zahl eine 0 ist
    smt2File << "(assert (= c_mantissa_underflow_0 (ite (= c_exponent_underflow comp_expo) (bvlshr c_mantissa_overflow shift_mant) c_mantissa_overflow)))" << endl;


    // Kontrollieren erstmla ob X oder b eine 0 ist:
    //smt2File << "(assert (= c_mantissa_zero (ite (or (and (= a_exponent comp_expo) (= a_mantissa_extra comp_mant)) (and (= b_exponent comp_expo) (= b_mantissa_extra comp_mant))) comp_mant c_mantissa_extra)))" << endl;

    // Also falls hier die exponente 0 ist, dann soll das Ergebnis erstmal denormalisiert werden.
    // Danach kommt die Vorschleife, um wie viele Nullen wir nahc rehcts shiften müssen.
    smt2File << "(declare-fun shift_time_underflow_c_0 () (_ BitVec " << exponentWidth + 1<< "))" << endl;
    smt2File << "(assert (= shift_time_underflow_c_0  (_ bv0 " << exponentWidth + 1 << ")))" << endl;

    smt2File << "(declare-fun take_last_bit_c_0 () (_ BitVec 1 ))" << endl;
    smt2File << "(assert (= take_last_bit_c_0 ((_ extract 0 0 ) c_mantissa_overflow)))" << endl;


    for (int i = 1; i < mant_length  + 10; i++) {
             smt2File << "(declare-fun shift_time_underflow_c_"<<i<<" () (_ BitVec " << exponentWidth + 1<< "))" << endl;
             smt2File << "(declare-fun c_mantissa_underflow_"<<i<<" () (_ BitVec " <<mant_length + 2<< "))" << endl;
             smt2File << "(declare-fun take_last_bit_c_"<<i<<" () (_ BitVec 1 ))" << endl;
    }

    for(int x = 1; x < mant_length  + 10; x++){
        smt2File << "(assert (= shift_time_underflow_c_"<< x <<" (ite (and (= c_exponent_underflow comp_expo)(bvugt count_underflow_c shift_time_underflow_c_"<< x - 1 <<")) (bvadd shift_time_underflow_c_"<< x - 1 <<"  add_shift) shift_time_underflow_c_"<< x - 1 <<")))" << endl;
        smt2File << "(assert (= take_last_bit_c_"<<x<<" (ite  (and (= c_exponent_underflow comp_expo)(bvugt count_underflow_c shift_time_underflow_c_"<< x - 1 <<")) ((_ extract 0 0 ) c_mantissa_underflow_"<< x - 1 <<") null)))" << endl;
        smt2File << "(assert (= c_mantissa_underflow_"<< x <<" (ite  (and (= c_exponent_underflow comp_expo)(bvugt count_underflow_c shift_time_underflow_c_"<< x - 1 <<")) (bvlshr c_mantissa_underflow_"<< x - 1 <<" shift_mant) c_mantissa_underflow_"<< x - 1 <<")))" << endl;
    }

    //smt2File << "(declare-fun get_outshiftet_numbers  () (_ BitVec " <<mant_length + 2<< "))" << endl;

    smt2File << "(declare-fun add_outshift_number_c_0 () (_ BitVec 1))" << endl;
    smt2File << "(assert (= add_outshift_number_c_0 take_last_bit_c_0))" << endl;



    for(int x = 1; x < mant_length + 10; x++) {
        smt2File << "(declare-fun add_outshift_number_c_"<<x<<" () (_ BitVec 1))" << endl;
        smt2File << "(assert (= add_outshift_number_c_"<<x<<" (ite (or (= add_outshift_number_c_"<<x - 1<<" eins)(= take_last_bit_c_"<<x - 1<<" eins)) eins null)))" << endl;
            //smt2File << "(assert (= s_outshift_ (ite (= take_last_bit_c_"<<x<<" null) null eins)))" << endl;
    }

    // Nachdem wir geshiftet haben, müssen wir nun die Manitssa Größe anpassen und mit dem GRS runden
    smt2File << "(assert (= c_mantissa (ite (and (or (and (= extra_bit_c_2 #b1)(= extra_bit_c #b1))(and (= extra_bit_c_2 #b1)(= extra_bit_c #b0)))(distinct c_exponent_underflow comp_expo)) ((_ extract "<<mant_length<<" "<<mantissaWidth + 1<<") c_mantissa_underflow_"<<mant_length  + 9<<")(ite (and (or (and (= extra_bit_c_2 #b1)(= extra_bit_c #b1))(= extra_bit_c #b0))(= c_exponent_underflow comp_expo)) ((_ extract "<<mant_length - 1 <<" "<<mantissaWidth  <<") c_mantissa_underflow_"<<mant_length  + 9<<") ((_ extract "<<mant_length - 1<<" "<< mantissaWidth<<") c_mantissa_underflow_"<<mant_length  + 9<<")))))" << endl;

    smt2File << "(assert (= c_mantissa_rest (ite (and (or (and (= extra_bit_c_2 #b1)(= extra_bit_c #b1))(and (= extra_bit_c_2 #b1)(= extra_bit_c #b0)))(distinct c_exponent_underflow comp_expo)) ((_ extract "<<mantissaWidth<<" 1) c_mantissa_underflow_"<<mant_length  + 9<<")(ite (and (or (and (= extra_bit_c_2 #b1)(= extra_bit_c #b1))(= extra_bit_c #b0))(= c_exponent_underflow comp_expo)) ((_ extract "<<mantissaWidth - 1 <<" 0 ) c_mantissa_underflow_"<<mant_length  + 9<<") ((_ extract "<< mantissaWidth - 1<<" 0) c_mantissa_underflow_"<<mant_length  + 9<<")))))" << endl;

    // auf und abrunden der Mantissa
    // Aufrunden
    // Fall 1:
    // G = 1 ,guard_bit_c = 1
    //Fall 2:
    //G = 1, R&S = 0 , guard_bit_c = 1
    //
    // Abrunden:
    // Fall 1:
    // G = 0 , guard_bit_c = 0
    // G = 1, R&S = 0 guard_bit_c = 0

    // wenn nach links geshiftet, dann ändern sich die Positionen der GRS.
    smt2File << "(assert (= g_ (ite (and (or (and (= extra_bit_c_2 #b1)(= extra_bit_c #b1))(and (= extra_bit_c_2 #b1)(= extra_bit_c #b0)))(distinct c_exponent_underflow comp_expo)) ((_ extract "<<mantissaWidth<<" "<<mantissaWidth<<") c_mantissa_underflow_"<<mant_length  + 9<<")(ite (and (or (and (= extra_bit_c_2 #b1)(= extra_bit_c #b1))(= extra_bit_c #b0))(= c_exponent_underflow comp_expo)) ((_ extract "<<mantissaWidth - 1 <<" "<<mantissaWidth - 1 <<") c_mantissa_underflow_"<<mant_length  + 9<<") ((_ extract "<<mantissaWidth - 1<<" "<< mantissaWidth - 1 <<") c_mantissa_underflow_"<<mant_length  + 9<<")))))" << endl;

    smt2File << "(assert (= r_(ite (and (or (and (= extra_bit_c_2 #b1)(= extra_bit_c #b1))(and (= extra_bit_c_2 #b1)(= extra_bit_c #b0)))(distinct c_exponent_underflow comp_expo)) ((_ extract "<<mantissaWidth - 1<<" "<<mantissaWidth - 1<<") c_mantissa_underflow_"<<mant_length  + 9<<")(ite (and (or (and (= extra_bit_c_2 #b1)(= extra_bit_c #b1))(= extra_bit_c #b0))(= c_exponent_underflow comp_expo)) ((_ extract "<<mantissaWidth - 2 <<" "<<mantissaWidth - 2 <<") c_mantissa_underflow_"<<mant_length  + 9<<") ((_ extract "<<mantissaWidth - 2<<" "<< mantissaWidth - 2 <<") c_mantissa_underflow_"<<mant_length  + 9<<")))))" << endl;

    smt2File << "(assert (= s_help_ (ite (and (or (and (= extra_bit_c_2 #b1)(= extra_bit_c #b1))(and (= extra_bit_c_2 #b1)(= extra_bit_c #b0)))(distinct c_exponent_underflow comp_expo)) ((_ extract "<<mantissaWidth-2<<" 1) c_mantissa_underflow_"<<mant_length  + 9<<")(ite (and (or (and (= extra_bit_c_2 #b1)(= extra_bit_c #b1))(= extra_bit_c #b0))(= c_exponent_underflow comp_expo)) ((_ extract "<<mantissaWidth - 3 <<" 0) c_mantissa_underflow_"<<mant_length  + 9<<") ((_ extract "<<mantissaWidth - 3<<" 0) c_mantissa_underflow_"<<mant_length  + 9<<")))))" << endl;

    smt2File << "(assert (= s_last_ (ite (and (or (and (= extra_bit_c_2 #b1)(= extra_bit_c #b1))(and (= extra_bit_c_2 #b1)(= extra_bit_c #b0)))(distinct c_exponent_underflow comp_expo)) ((_ extract 0 0) c_mantissa_underflow_"<<mant_length  + 9<<") null)))" << endl;

    smt2File << "(assert (= s_ (concat s_help_ s_last_)))" << endl;
    // Zum Runden ist das guard_bit_c wichtig, da es dazu dient dass es gerundet wird.
    smt2File << "(assert (= lsb_ (ite (and (or (and (= extra_bit_c_2 #b1)(= extra_bit_c #b1))(and (= extra_bit_c_2 #b1)(= extra_bit_c #b0)))(distinct c_exponent_underflow comp_expo)) ((_ extract "<<mantissaWidth + 1<<" "<<mantissaWidth + 1<<") c_mantissa_underflow_"<<mant_length  + 9<<")(ite (and (or (and (= extra_bit_c_2 #b1)(= extra_bit_c #b1))(= extra_bit_c #b0))(= c_exponent_underflow comp_expo)) ((_ extract "<<mantissaWidth  <<" "<<mantissaWidth  <<") c_mantissa_underflow_"<<mant_length  + 9<<") ((_ extract "<<mantissaWidth <<" "<< mantissaWidth<<") c_mantissa_underflow_"<<mant_length  + 9<<")))))" << endl;

    //0101
    //1100
    //1111
    //0111
    //1101
    //0101
    //1101

    //nur Aufrundfälle aufzählen, da beim abrunden, die z_mantisse nicht geändert wird sondern nur gecuttet
    smt2File << "(assert (= c_mantissa_GRS(ite (or (and (= g_ #b1) (or (= r_#b1) (distinct s_ compare_s)(= add_outshift_number_c_"<<mant_length + 9 <<" eins))) (and (= g_ #b1) (= lsb_ #b1))) (bvadd c_mantissa add_mant) c_mantissa)))" << endl;

    smt2File << "(assert (= c_exponent_over_ (ite (and (= c_mantissa comp_mant_1) (= c_mantissa_GRS comp_mant_0)) (bvadd c_exponent_underflow add_expo)  c_exponent_underflow)))" << endl;


    smt2File << "(assert (= c_mantissa_NaN (ite (or (and (= a_exponent comp_expo_1) (distinct a_mantissa_extra comp_mant)) (and (= b_exponent comp_expo_1) (distinct b_mantissa_extra comp_mant))) comp_mant_1 c_mantissa_GRS)))" << endl;

    // concat everything_ and compare with fp
    smt2File << "(assert (= c (concat c_sign c_exponent_over_ )))" << endl;
    smt2File << "(assert (= c_finale (concat c c_mantissa_NaN)))" << endl;

    smt2File << "(assert (= x b))" << endl;
    smt2File << "(assert (= y a))" << endl;

    //Verschieden
    smt2File << "(assert (distinct z_finale c_finale))" << endl;

    //Gleich
    // smt2File << "(assert (= z_finale c_finale))" << endl;

    smt2File << "(check-sat)" << endl;
    //smt2File << "(get-model)" << endl;
    //smt2File << "(get-value(x y z_finale a b c_finale))" << endl;
    smt2File << "(exit)" << endl;
    smt2File.close();

    cout << signWidth << endl;
    cout << exponentWidth << endl;
    cout << mantissaWidth << endl;
    cout << mant_length << endl;
    cout << length_max << endl;


    cout << "SMT2-Datei erfolgreich erstellt: BV_BV"+sizebit+"_multiplication.smt2 "<< endl;
    return 0;
}

int fp_fp(string sizebit) {
        // input variablen
        // in this case: bitsize8
        // 1sign 4expo 3mantisse
        fstream smt2File;
        smt2File.open("FP"+sizebit+".smt2",ios::out);
        smt2File << ";;; floating_point"+sizebit+" multiplication binary" << endl;

        smt2File << endl;
        smt2File << "(set-info :source |Benny Wennberg Bachelor thesis|)" << endl;
        // ab hier Code

        // Schreiben von SMT2-Inhalten in die Datei
    smt2File << "(set-logic QF_BVFP)" << endl; // Verwendung von QF_FPBV für Floating-Point Arithmetic

    // Deklaration von Gleitkommazahlen x, y und z
    int length_max = stoi(sizebit);
    if (length_max == 16) {
        smt2File << "(declare-fun x_fp () (_ FloatingPoint 5 11))" << endl; // Single Precision: 8 Bit für den Exponenten, 24 Bit für die Mantisse
        smt2File << "(declare-fun y_fp () (_ FloatingPoint 5 11))" << endl;
        smt2File << "(declare-fun z_fp () (_ FloatingPoint 5 11))" << endl;
    } else if (length_max == 128) {
        smt2File << "(declare-fun x_fp () (_ FloatingPoint 15 113))" << endl; // Single Precision: 8 Bit für den Exponenten, 24 Bit für die Mantisse
        smt2File << "(declare-fun y_fp () (_ FloatingPoint 15 113))" << endl;
        smt2File << "(declare-fun z_fp () (_ FloatingPoint 15 113))" << endl;
    } else if (length_max == 32) {
        // Deklaration von Gleitkommazahlen x, y und z
        smt2File << "(declare-fun x_fp () (_ FloatingPoint 8 24))" << endl; // Single Precision: 8 Bit für den Exponenten, 24 Bit für die Mantisse
        smt2File << "(declare-fun y_fp () (_ FloatingPoint 8 24))" << endl;
        smt2File << "(declare-fun z_fp () (_ FloatingPoint 8 24))" << endl;
    } else if (length_max == 64) {
        smt2File << "(declare-fun x_fp () (_ FloatingPoint 11 53))" << endl; // Single Precision: 8 Bit für den Exponenten, 24 Bit für die Mantisse
        smt2File << "(declare-fun y_fp () (_ FloatingPoint 11 53))" << endl;
        smt2File << "(declare-fun z_fp () (_ FloatingPoint 11 53))" << endl;
    }
    // x = 109999111100000000111100000000110
    // y = 10111111000000000000000000000110

    /*// Setzen von Werten für x und y
    smt2File << "(assert (= x_fp (fp #b0 #b01111111 #b00000000111100000000110)))" << endl; // x = 0.5 (Exponent: 126, Mantisse: 0)
    smt2File << "(assert (= y_fp (fp #b0 #b01111110 #b00111000000000000001111)))" << endl; // y = 0.125 (Exponent: 124, Mantisse: 0)
*/



    // Operationen mit Floating-Point Zahlen (Multiplikation)
    smt2File << "(assert (= z_fp (fp.mul RNE  x_fp y_fp)))" << endl; // Multiplikation von x und y

    // --------------------------------------------------------------------------------------
    // Ab hier wird Kommutativ kotrolliert mit FP
    // Deklaration von Gleitkommazahlen x, y und z
    if (length_max == 16) {
        smt2File << "(declare-fun a_fp () (_ FloatingPoint 5 11))" << endl; // Single Precision: 8 Bit für den Exponenten, 24 Bit für die Mantisse
        smt2File << "(declare-fun b_fp () (_ FloatingPoint 5 11))" << endl;
        smt2File << "(declare-fun c_fp () (_ FloatingPoint 5 11))" << endl;
    } else if (length_max == 128) {
        smt2File << "(declare-fun a_fp () (_ FloatingPoint 15 113))" << endl; // Single Precision: 8 Bit für den Exponenten, 24 Bit für die Mantisse
        smt2File << "(declare-fun b_fp () (_ FloatingPoint 15 113))" << endl;
        smt2File << "(declare-fun c_fp () (_ FloatingPoint 15 113))" << endl;
    } else if (length_max == 32) {
        // Deklaration von Gleitkommazahlen x, y und z
        smt2File << "(declare-fun a_fp () (_ FloatingPoint 8 24))" << endl; // Single Precision: 8 Bit für den Exponenten, 24 Bit für die Mantisse
        smt2File << "(declare-fun b_fp () (_ FloatingPoint 8 24))" << endl;
        smt2File << "(declare-fun c_fp () (_ FloatingPoint 8 24))" << endl;
    } else if (length_max == 64) {
        smt2File << "(declare-fun a_fp () (_ FloatingPoint 11 53))" << endl; // Single Precision: 8 Bit für den Exponenten, 24 Bit für die Mantisse
        smt2File << "(declare-fun b_fp () (_ FloatingPoint 11 53))" << endl;
        smt2File << "(declare-fun c_fp () (_ FloatingPoint 11 53))" << endl;
    }

    // Operationen mit Floating-Point Zahlen (Multiplikation)
    smt2File << "(assert (= c_fp (fp.mul RNE  a_fp b_fp)))" << endl; // Multiplikation von x und y

    smt2File << "(assert (= x_fp b_fp))" << endl;
    smt2File << "(assert (= y_fp a_fp))" << endl;
    //Verschieden
    smt2File << "(assert (distinct z_fp c_fp))" << endl;

    smt2File << "(check-sat)" << endl;
    //smt2File << "(get-model)" << endl;
    //smt2File << "(get-value (x_fp y_fp z_fp))" << endl; // Abrufen der Werte von x, y und z;

    cout << "SMT2-Datei erfolgreich erstellt: FP"+sizebit+".smt2" << endl;
}


int bv_fp(string sizebit, int sign, int exponent,int mantissa) {

        fstream smt2File;
        smt2File.open("FP_BV_"+sizebit+"_multiplication.smt2",ios::out);
        smt2File << ";;; bfloat"+sizebit+" multiplication fp_binary" << endl;
        smt2File << "(set-option :produce-models true)" << endl;
        smt2File << "(set-logic QF_BVFP)" << endl; // Verwendung von QF_FPBV für Floating-Point Arithmetic
        smt2File << endl;
        smt2File << "(set-info :source |Benny Wennberg Bachelor thesis|)" << endl;        // ab hier Code

        // Schreiben von SMT2-Inhalten in die Datei

    // input variablen
    int signWidth = sign;
    int exponentWidth = exponent;
    int mantissaWidth = mantissa;
    int mant_length = mantissaWidth * 2;
    int length_max = stoi(sizebit);


    // Deklaration von festen Bit-Vektoren für Vorzeichen, Exponent und Mantisse für x, y und z
    smt2File <<  "(declare-fun eins () (_ BitVec " << signWidth << "))" << endl;
    smt2File << "(assert (= eins  #b1 ))" << endl;
    smt2File <<  "(declare-fun null () (_ BitVec " << signWidth << "))" << endl;
    smt2File << "(assert (= null  #b0 ))" << endl;

    smt2File <<  "(declare-fun compare_s () (_ BitVec " << mantissaWidth - 1<< "))" << endl;
    smt2File << "(assert (= compare_s  (_ bv0 " << mantissaWidth - 1<< ")))" << endl;

    smt2File << "(declare-fun comp_expo () (_ BitVec " << exponentWidth<<"))" << endl;
    smt2File << "(assert (= comp_expo  (_ bv0 " << exponentWidth << ")))" << endl;
    smt2File << "(declare-fun comp_mant () (_ BitVec " << mant_length + 2<<"))" << endl;
    smt2File << "(assert (= comp_mant  (_ bv0 " << mant_length + 2 << ")))" << endl;
    smt2File << "(declare-fun comp_mant_0 () (_ BitVec " << mantissaWidth<<"))" << endl;
    smt2File << "(assert (= comp_mant_0  (_ bv0 " << mantissaWidth << ")))" << endl;

    smt2File << "(declare-fun comp_expo_1 () (_ BitVec " << exponentWidth<<"))" << endl;
    smt2File << "(declare-fun comp_mant_1 () (_ BitVec " << mantissaWidth<<"))" << endl;
    if (length_max == 16) {
        smt2File << "(assert (= comp_mant_1 #b1111111111))" << endl;
        smt2File << "(assert (= comp_expo_1 #b11111))" << endl;
    } else if (length_max == 128) {
        smt2File << "(assert (= comp_mant_1 #b1111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111))" << endl;
        smt2File << "(assert (= comp_expo_1 #b111111111111111))" << std::endl;
    } else if (length_max == 32) {
         smt2File << "(assert (= comp_mant_1 #b11111111111111111111111))" << endl;
         smt2File << "(assert (= comp_expo_1 #b11111111))" << std::endl;
    } else if (length_max == 64) {
         smt2File << "(assert (= comp_mant_1 #b1111111111111111111111111111111111111111111111111111))" << endl;
         smt2File << "(assert (= comp_expo_1 #b11111111111))" << std::endl;
    }


    smt2File << "(declare-fun add_expo_0 () (_ BitVec " << exponentWidth - 1<<"))" << endl;
    smt2File << "(assert (= add_expo_0  (_ bv0 " << exponentWidth - 1 << ")))" << endl;
    smt2File << "(declare-fun add_expo () (_ BitVec " << exponentWidth <<"))" << endl;
    smt2File << "(assert (= add_expo (concat add_expo_0 eins)))" << endl;

    smt2File << "(declare-fun add_mant_0 () (_ BitVec " << mantissaWidth - 1<<"))" << endl;
    smt2File << "(assert (= add_mant_0  (_ bv0 " << mantissaWidth - 1 << ")))" << endl;
    smt2File << "(declare-fun add_mant () (_ BitVec " << mantissaWidth <<"))" << endl;
    smt2File << "(assert (= add_mant (concat add_mant_0 eins)))" << endl;


    smt2File << "(declare-fun add_shift_0 () (_ BitVec " << exponentWidth<<"))" << endl;
    smt2File << "(assert (= add_shift_0  (_ bv0 " << exponentWidth << ")))" << endl;
    smt2File << "(declare-fun add_shift () (_ BitVec " << exponentWidth + 1 <<"))" << endl;
    smt2File << "(assert (= add_shift (concat add_shift_0 eins)))" << endl;

    smt2File << "(declare-fun shift_mant_0 () (_ BitVec " << mant_length + 1<<"))" << endl;
    smt2File << "(assert (= shift_mant_0  (_ bv0 " << mant_length + 1 << ")))" << endl;
    smt2File << "(declare-fun shift_mant () (_ BitVec " << mant_length + 2<<"))" << endl;
    smt2File << "(assert (= shift_mant (concat shift_mant_0 eins)))" << endl;

    smt2File << "(declare-fun x () (_ BitVec " << length_max << "))" << endl;
    smt2File << "(declare-fun x_sign () (_ BitVec " << signWidth << "))" << endl;
    smt2File << "(declare-fun x_exponent () (_ BitVec " << exponentWidth << "))" << endl;
    smt2File << "(declare-fun x_mantissa () (_ BitVec " << mantissaWidth << "))" << endl;

    smt2File << "(declare-fun y () (_ BitVec " << length_max << "))" << endl;
    smt2File << "(declare-fun y_sign () (_ BitVec " << signWidth << "))" << endl;
    smt2File << "(declare-fun y_exponent () (_ BitVec " << exponentWidth << "))" << endl;
    smt2File << "(declare-fun y_mantissa () (_ BitVec " << mantissaWidth << "))" << endl;

        // extend Mantissa for multiplication
    smt2File << "(declare-fun x_exponent_extra () (_ BitVec " << exponentWidth + 1 << "))" << endl;
    smt2File << "(declare-fun y_exponent_extra () (_ BitVec " << exponentWidth + 1<< "))" << endl;
    smt2File << "(declare-fun z_exponent_extra_help () (_ BitVec " << exponentWidth + 1<< "))" << endl;
    smt2File << "(declare-fun z_exponent_extra () (_ BitVec " << exponentWidth + 1<< "))" << endl;

    // extend Mantissa for multiplication
    smt2File << "(declare-fun x_mantissa_extra () (_ BitVec " << mant_length + 2 << "))" << endl;
    smt2File << "(declare-fun y_mantissa_extra () (_ BitVec " << mant_length + 2<< "))" << endl;
    smt2File << "(declare-fun z_mantissa_extra () (_ BitVec " << mant_length + 2<< "))" << endl;


   // Get the extended Mantissa with beginning bit
    smt2File << "(declare-fun  nullen_0 () (_ BitVec " << mantissaWidth + 1 << "))" << endl;
    smt2File << "(assert (= nullen_0  (_ bv0 " << mantissaWidth + 1 << ")))" << endl;
    smt2File << "(declare-fun  nullen_1 () (_ BitVec " << mantissaWidth + 2 << "))" << endl;
    smt2File << "(assert (= nullen_1 (concat nullen_0 eins)))" << endl;

    smt2File << "(declare-fun  nullen_00 () (_ BitVec " << mantissaWidth + 2 << "))" << endl;
    smt2File << "(assert (= nullen_00 (_ bv0 " << mantissaWidth + 2 << ")))" << endl;

    // Z variablen
    smt2File << "(declare-fun z () (_ BitVec " << signWidth + exponentWidth << "))" << endl;
    smt2File << "(declare-fun z_finale () (_ BitVec " << length_max << "))" << endl;

    smt2File << "(declare-fun z_sign () (_ BitVec " << signWidth << "))" << endl;

    smt2File << "(declare-fun z_exponent () (_ BitVec " << exponentWidth << "))" << endl;
    smt2File << "(declare-fun z_exponent_GRS () (_ BitVec " << exponentWidth << "))" << endl;
    smt2File << "(declare-fun z_exponent_deNorm () (_ BitVec " << exponentWidth << "))" << endl;
    smt2File << "(declare-fun z_exponent_zero () (_ BitVec " << exponentWidth << "))" << endl;
    smt2File << "(declare-fun z_exponent_overflow () (_ BitVec " << exponentWidth << "))" << endl;
    smt2File << "(declare-fun z_exponent_underflow () (_ BitVec " << exponentWidth << "))" << endl;
    smt2File << "(declare-fun z_exponent_over () (_ BitVec " << exponentWidth << "))" << endl;

    smt2File << "(declare-fun z_mantissa () (_ BitVec " << mantissaWidth  << "))" << endl;
    smt2File << "(declare-fun z_mantissa_rest () (_ BitVec " << mantissaWidth  << "))" << endl;
    smt2File << "(declare-fun z_mantissa_GRS () (_ BitVec " << mantissaWidth  << "))" << endl;
    smt2File << "(declare-fun z_mantissa_zero () (_ BitVec " << mant_length + 2 << "))" << endl;
    smt2File << "(declare-fun z_mantissa_overflow () (_ BitVec " << mant_length + 2 << "))" << endl;
    smt2File << "(declare-fun z_mantissa_underflow_0 () (_ BitVec " << mant_length + 2 << "))" << endl;
    smt2File << "(declare-fun z_mantissa_NaN () (_ BitVec " << mantissaWidth << "))" << endl;


    // Addition hilfe Bias muss noch je nach Bitsize um (bei 32 bit um 127 abgezogen werden.)
    smt2File << "(declare-fun bias () (_ BitVec " << exponentWidth << "))" << endl;
    smt2File << "(declare-fun bias_inf_compare () (_ BitVec " << exponentWidth << "))" << endl;
    smt2File << "(declare-fun bias_extra () (_ BitVec " << exponentWidth +1<< "))" << endl;
    smt2File << "(declare-fun bias_compare_underflow () (_ BitVec " << exponentWidth +1<< "))" << endl;
    smt2File << "(declare-fun bias_compare_overflow () (_ BitVec " << exponentWidth +1<< "))" << endl;
    // Der Bias-Wert für IEEE 754 (127 für 8-Bit Exponenten)
   if (length_max == 16) {
        smt2File << "(assert (= bias #b01111))" << endl; // 15
        smt2File << "(assert (= bias_inf_compare #b11111))" << endl; // 31
        smt2File << "(assert (= bias_extra #b001111))" << endl;
        smt2File << "(assert (= bias_compare_overflow #b101110))" << endl; // 46, 46 - 15 = 31 -> overflow
        smt2File << "(assert (= bias_compare_underflow #b001111))" << endl; // 15, 14 - 15 = -1 -> underflow
   } else if (length_max == 128) {
        smt2File << "(assert (= bias #b01111111111))" << endl; // 1023
        smt2File << "(assert (= bias_inf_compare #b11111111111))" << endl; // 2047
        smt2File << "(assert (= bias_extra #b0011111111111))" << endl;
        smt2File << "(assert (= bias_compare_overflow #b101111111110))" << endl; // 3070, 3070 - 1023 = 2047 -> overflow
        smt2File << "(assert (= bias_compare_underflow #b001111111111))" << endl; // 1023, 1022 - 1023 = -1 -> underflow
   } else if (length_max == 32) {
        smt2File << "(assert (= bias #b01111111))" << endl; // 127
        smt2File << "(assert (= bias_inf_compare #b11111111))" << endl; // 255
        smt2File << "(assert (= bias_extra #b001111111))" << endl;
        smt2File << "(assert (= bias_compare_overflow #b101111110))" << endl; // 382, 382 - 127 = 255 -> overflow
        smt2File << "(assert (= bias_compare_underflow #b001111111))" << endl; // 127, 126 - 127 = -1 -> underflow
   } else if (length_max == 64) {
        smt2File << "(assert (= bias #b01111111111))" << endl; // 1023
        smt2File << "(assert (= bias_inf_compare #b11111111111))" << endl; // 2047
        smt2File << "(assert (= bias_extra #b001111111111))" << endl;
        smt2File << "(assert (= bias_compare_overflow #b101111111110))" << endl; // 3070, 3070 - 1023 = 2047 -> overflow
        smt2File << "(assert (= bias_compare_underflow #b001111111111))" << endl; // 1023, 1022 - 10237 = -1 -> underflow
   }

    smt2File << "(declare-fun g () (_ BitVec 1))" << endl;
    smt2File << "(declare-fun r () (_ BitVec 1))" << endl;
    smt2File << "(declare-fun s_help  () (_ BitVec "<< mantissaWidth - 2 <<"))" << endl;
    smt2File << "(declare-fun s_last () (_ BitVec 1))" << endl;
    smt2File << "(declare-fun s_outshift () (_ BitVec 1))" << endl;
    smt2File << "(declare-fun s  () (_ BitVec "<< mantissaWidth - 1 <<"))" << endl;

    smt2File << "(declare-fun lsb () (_ BitVec 1))" << endl;
    
/*
    string binary_x;
    string binary_y;

   if (length_max == 16) {
        binary_x = "0001000111000000";
        binary_y = "0000110100101100";
   } else if (length_max == 8) {
        binary_x = "01110000";
        binary_y = "01111111";
   } else if (length_max == 32) {
        binary_x = "01100011100000111110000000000000";
        binary_y = "00000000000000000000000000000000";
   } else if (length_max == 64) {
        binary_x = "0111111110000000000000001111111100000000000000000000000000000000";
        binary_y = "0100111110011100000000000011111111000000000000000000000000000111";
   }

   smt2File << "(assert (= x #b" << binary_x << "))" << endl;
    smt2File << "(assert (= y #b" << binary_y << "))" << endl;
*/
   // exract sign, expo and mant
    // Vorzeichen extrahieren
    smt2File << ";;; exract sign mantissa expo" << endl;

    smt2File << "(assert (= x_sign ((_ extract " << length_max - 1 << " " << length_max - 1 << ") x)))" << endl;
    smt2File << "(assert (= y_sign ((_ extract " << length_max - 1 << " " << length_max - 1 << ") y)))" << endl;

    smt2File << "(assert (= x_exponent ((_ extract " << length_max - 2 << " " << length_max - 1 - exponentWidth << ") x)))" << endl;
    smt2File << "(assert (= y_exponent ((_ extract " << length_max - 2 << " " << length_max - 1 - exponentWidth << ") y)))" << endl;

    smt2File << "(assert (= x_mantissa ((_ extract " << mantissaWidth - 1 << " 0) x)))" << endl;
    smt2File << "(assert (= y_mantissa ((_ extract " << length_max - 2 - exponentWidth << " 0) y)))" << endl;

    // Denormalized Numbers, which extend the mantissa without the extra bit.
    smt2File << "(assert (= x_mantissa_extra  (ite (= x_exponent comp_expo)(concat nullen_00 x_mantissa) (concat nullen_1 x_mantissa))))" << endl;
    smt2File << "(assert (= y_mantissa_extra  (ite (= y_exponent comp_expo)(concat nullen_00 y_mantissa) (concat nullen_1 y_mantissa))))" << endl;

    // Erweitern des Exponenten für Overflow
    smt2File << "(assert (= x_exponent_extra  (concat null x_exponent)))" << endl;
    smt2File << "(assert (= y_exponent_extra  (concat null y_exponent)))" << endl;
    smt2File << "(assert (= z_exponent_extra_help (bvadd x_exponent_extra y_exponent_extra)))" << endl;
    smt2File << "(assert (= z_exponent_extra(bvsub (bvadd x_exponent_extra y_exponent_extra) bias_extra)))" << endl;

    // Berechnung von z_sign als XOR von x_sign und y_sign
    smt2File << "(assert (= z_sign (bvxor x_sign y_sign)))" << endl;

   // Berechnung von z_exponent als Addition von x_exponent und y_exponent + Abzug der Bias (bfloat32 = 127)
    smt2File << "(assert (= z_exponent(bvsub (bvadd x_exponent y_exponent) bias)))" << endl;

    // Berechnung von z_mantissa als Multiplikation von x_mantissa und y_mantissa
    smt2File << "(assert (= z_mantissa_extra (bvmul x_mantissa_extra y_mantissa_extra)))" << endl;

    // Testen auf Normalisierung,ob der radix-point verschoben werden soll
    smt2File << "(declare-fun extra_bit () (_ BitVec 1))" << endl;
    smt2File << "(declare-fun extra_bit_2 () (_ BitVec 1))" << endl;
    smt2File << "(assert (= extra_bit (ite (or (= y_exponent comp_expo) (= x_exponent comp_expo)) eins ((_ extract "<<mant_length << " " << mant_length<<") z_mantissa_extra))))" << endl;
    smt2File << "(assert (= extra_bit_2 (ite (or (= y_exponent comp_expo) (= x_exponent comp_expo)) eins ((_ extract "<<mant_length + 1 << " " << mant_length + 1<<") z_mantissa_extra))))" << endl;
    //smt2File << "(assert (= extra_bit (ite (or (= y_exponent comp_expo) (= x_exponent comp_expo)) eins ((_ extract 2 2  ) z_mantissa_extra))))" << endl;
    //smt2File << "(assert (= extra_bit_2 (ite (or (= y_exponent comp_expo) (= x_exponent comp_expo)) eins ((_ extract 1 1) z_mantissa_extra))))" << endl;

    // Wenn nach links geshiftet wird die Exponente um 1 addiert
    smt2File << "(assert (= z_exponent_GRS (ite (and (or (and (= extra_bit_2 #b1)(= extra_bit #b1))(and (= extra_bit_2 #b1)(= extra_bit #b0)))(distinct z_exponent bias_inf_compare)) (bvadd z_exponent add_expo) z_exponent)))" << endl;

    //Denormalized Number, heißt es wird normal gerechnet wie immer, aber am ende ist die zahl dennoch denormalizied
    //smt2File<< "(assert (= z_exponent_deNorm (ite (or (= x_exponent comp_expo) (= y_exponent comp_expo)) comp_expo  z_exponent_GRS)))" << endl;

    // wenn einer der beiden Inputs 0 ist = soll es auhc null bleiben
   smt2File << "(assert (= z_exponent_zero (ite (or (and (= x_exponent comp_expo) (= x_mantissa_extra comp_mant )) (and (= y_exponent comp_expo) (= y_mantissa_extra comp_mant))) comp_expo z_exponent_GRS)))" << endl;

    // INF +  overflow Exponent
    smt2File << "(assert (= z_exponent_overflow (ite (or (= x_exponent comp_expo_1) (= y_exponent comp_expo_1)(= z_exponent_GRS comp_expo_1) (bvugt z_exponent_extra_help bias_compare_overflow)) comp_expo_1 z_exponent_zero)))" << endl;

    // Underflow
    smt2File << "(assert (= z_exponent_underflow (ite (bvugt bias_compare_underflow  z_exponent_extra_help ) comp_expo z_exponent_overflow)))" << endl;

    // Plan: ich habe das Minimum von #b1111 was
    // der Plan ist die Anzahl Nullen zu zählen indem ich #1111 - z_exponent_extra_help
    // falls z_exponent_extra_help kleiner ist.
    // Zählt die Anzahl Nullen nach dem radix Point
    smt2File << "(declare-fun count_underflow () (_ BitVec " << exponentWidth + 1<< "))" << endl;
    smt2File << "(assert (= count_underflow (ite (bvugt bias_compare_underflow  z_exponent_extra_help ) (bvsub bias_extra z_exponent_extra_help) (concat null comp_expo))))" << endl;

    // DH. Wenn EXPO = 0, dann solte erstmal einmalig nach rechts geshiftet werden.

    // Wir haben hier nur z_mantissa_extra
    // Overflow
    // Kontrollieren ob die Exponente zum Overflow wurde:
    smt2File << "(assert (= z_mantissa_overflow (ite (or (and (= x_exponent comp_expo_1)(= x_mantissa_extra comp_mant ))(and (= y_exponent comp_expo_1)(= y_mantissa_extra comp_mant))(= z_exponent_underflow comp_expo_1) (bvugt z_exponent_extra_help bias_compare_overflow)) comp_mant z_mantissa_extra)))" << endl;

    //

    // Underflow
    // Dann wird geschaut ob die z_exponente ein denormalized Nummer ist: Wenn ja wird einmal nach rechts geshiftet sodass die erste zahl eine 0 ist
    smt2File << "(assert (= z_mantissa_underflow_0 (ite (= z_exponent_underflow comp_expo) (bvlshr z_mantissa_overflow shift_mant) z_mantissa_overflow)))" << endl;


    // Kontrollieren erstmla ob X oder Y eine 0 ist:
    //smt2File << "(assert (= z_mantissa_zero (ite (or (and (= x_exponent comp_expo) (= x_mantissa_extra comp_mant)) (and (= y_exponent comp_expo) (= y_mantissa_extra comp_mant))) comp_mant z_mantissa_extra)))" << endl;

    // Also falls hier die exponente 0 ist, dann soll das Ergebnis erstmal denormalisiert werden.
    // Danach kommt die Vorschleife, um wie viele Nullen wir nahc rehcts shiften müssen.
    smt2File << "(declare-fun shift_time_underflow_0 () (_ BitVec " << exponentWidth + 1<< "))" << endl;
    smt2File << "(assert (= shift_time_underflow_0  (_ bv0 " << exponentWidth + 1 << ")))" << endl;

    smt2File << "(declare-fun take_last_bit_0 () (_ BitVec 1 ))" << endl;
    smt2File << "(assert (= take_last_bit_0 ((_ extract 0 0 ) z_mantissa_overflow)))" << endl;


    for (int i = 1; i < mant_length  + 10; i++) {
             smt2File << "(declare-fun shift_time_underflow_"<<i<<" () (_ BitVec " << exponentWidth + 1<< "))" << endl;
             smt2File << "(declare-fun z_mantissa_underflow_"<<i<<" () (_ BitVec " <<mant_length + 2<< "))" << endl;
             smt2File << "(declare-fun take_last_bit_"<<i<<" () (_ BitVec 1 ))" << endl;
    }

    for(int x = 1; x < mant_length  + 10; x++){
        smt2File << "(assert (= shift_time_underflow_"<< x <<" (ite (and (= z_exponent_underflow comp_expo)(bvugt count_underflow shift_time_underflow_"<< x - 1 <<")) (bvadd shift_time_underflow_"<< x - 1 <<"  add_shift) shift_time_underflow_"<< x - 1 <<")))" << endl;
        smt2File << "(assert (= take_last_bit_"<<x<<" (ite  (and (= z_exponent_underflow comp_expo)(bvugt count_underflow shift_time_underflow_"<< x - 1 <<")) ((_ extract 0 0 ) z_mantissa_underflow_"<< x - 1 <<") null)))" << endl;
        smt2File << "(assert (= z_mantissa_underflow_"<< x <<" (ite  (and (= z_exponent_underflow comp_expo)(bvugt count_underflow shift_time_underflow_"<< x - 1 <<")) (bvlshr z_mantissa_underflow_"<< x - 1 <<" shift_mant) z_mantissa_underflow_"<< x - 1 <<")))" << endl;
    }

    //smt2File << "(declare-fun get_outshiftet_numbers  () (_ BitVec " <<mant_length + 2<< "))" << endl;

    smt2File << "(declare-fun add_outshift_number_0 () (_ BitVec 1))" << endl;
    smt2File << "(assert (= add_outshift_number_0 take_last_bit_0))" << endl;



    for(int x = 1; x < mant_length + 10; x++) {
        smt2File << "(declare-fun add_outshift_number_"<<x<<" () (_ BitVec 1))" << endl;
        smt2File << "(assert (= add_outshift_number_"<<x<<" (ite (or (= add_outshift_number_"<<x - 1<<" eins)(= take_last_bit_"<<x - 1<<" eins)) eins null)))" << endl;
            //smt2File << "(assert (= s_outshift (ite (= take_last_bit_"<<x<<" null) null eins)))" << endl;
    }

    // Nachdem wir geshiftet haben, müssen wir nun die Manitssa Größe anpassen und mit dem GRS runden
    smt2File << "(assert (= z_mantissa (ite (and (or (and (= extra_bit_2 #b1)(= extra_bit #b1))(and (= extra_bit_2 #b1)(= extra_bit #b0)))(distinct z_exponent_underflow comp_expo)) ((_ extract "<<mant_length<<" "<<mantissaWidth + 1<<") z_mantissa_underflow_"<<mant_length  + 9<<")(ite (and (or (and (= extra_bit_2 #b1)(= extra_bit #b1))(= extra_bit #b0))(= z_exponent_underflow comp_expo)) ((_ extract "<<mant_length - 1 <<" "<<mantissaWidth  <<") z_mantissa_underflow_"<<mant_length  + 9<<") ((_ extract "<<mant_length - 1<<" "<< mantissaWidth<<") z_mantissa_underflow_"<<mant_length  + 9<<")))))" << endl;

    smt2File << "(assert (= z_mantissa_rest (ite (and (or (and (= extra_bit_2 #b1)(= extra_bit #b1))(and (= extra_bit_2 #b1)(= extra_bit #b0)))(distinct z_exponent_underflow comp_expo)) ((_ extract "<<mantissaWidth<<" 1) z_mantissa_underflow_"<<mant_length  + 9<<")(ite (and (or (and (= extra_bit_2 #b1)(= extra_bit #b1))(= extra_bit #b0))(= z_exponent_underflow comp_expo)) ((_ extract "<<mantissaWidth - 1 <<" 0 ) z_mantissa_underflow_"<<mant_length  + 9<<") ((_ extract "<< mantissaWidth - 1<<" 0) z_mantissa_underflow_"<<mant_length  + 9<<")))))" << endl;

    // auf und abrunden der Mantissa
    // Aufrunden
    // Fall 1:
    // G = 1 ,Guard_bit = 1
    //Fall 2:
    //G = 1, R&S = 0 , Guard_bit = 1
    //
    // Abrunden:
    // Fall 1:
    // G = 0 , Guard_bit = 0
    // G = 1, R&S = 0 Guard_bit = 0

    // wenn nach links geshiftet, dann ändern sich die Positionen der GRS.
    smt2File << "(assert (= g (ite (and (or (and (= extra_bit_2 #b1)(= extra_bit #b1))(and (= extra_bit_2 #b1)(= extra_bit #b0)))(distinct z_exponent_underflow comp_expo)) ((_ extract "<<mantissaWidth<<" "<<mantissaWidth<<") z_mantissa_underflow_"<<mant_length  + 9<<")(ite (and (or (and (= extra_bit_2 #b1)(= extra_bit #b1))(= extra_bit #b0))(= z_exponent_underflow comp_expo)) ((_ extract "<<mantissaWidth - 1 <<" "<<mantissaWidth - 1 <<") z_mantissa_underflow_"<<mant_length  + 9<<") ((_ extract "<<mantissaWidth - 1<<" "<< mantissaWidth - 1 <<") z_mantissa_underflow_"<<mant_length  + 9<<")))))" << endl;

    smt2File << "(assert (= r (ite (and (or (and (= extra_bit_2 #b1)(= extra_bit #b1))(and (= extra_bit_2 #b1)(= extra_bit #b0)))(distinct z_exponent_underflow comp_expo)) ((_ extract "<<mantissaWidth - 1<<" "<<mantissaWidth - 1<<") z_mantissa_underflow_"<<mant_length  + 9<<")(ite (and (or (and (= extra_bit_2 #b1)(= extra_bit #b1))(= extra_bit #b0))(= z_exponent_underflow comp_expo)) ((_ extract "<<mantissaWidth - 2 <<" "<<mantissaWidth - 2 <<") z_mantissa_underflow_"<<mant_length  + 9<<") ((_ extract "<<mantissaWidth - 2<<" "<< mantissaWidth - 2 <<") z_mantissa_underflow_"<<mant_length  + 9<<")))))" << endl;

    smt2File << "(assert (= s_help (ite (and (or (and (= extra_bit_2 #b1)(= extra_bit #b1))(and (= extra_bit_2 #b1)(= extra_bit #b0)))(distinct z_exponent_underflow comp_expo)) ((_ extract "<<mantissaWidth-2<<" 1) z_mantissa_underflow_"<<mant_length  + 9<<")(ite (and (or (and (= extra_bit_2 #b1)(= extra_bit #b1))(= extra_bit #b0))(= z_exponent_underflow comp_expo)) ((_ extract "<<mantissaWidth - 3 <<" 0) z_mantissa_underflow_"<<mant_length  + 9<<") ((_ extract "<<mantissaWidth - 3<<" 0) z_mantissa_underflow_"<<mant_length  + 9<<")))))" << endl;

    smt2File << "(assert (= s_last (ite (and (or (and (= extra_bit_2 #b1)(= extra_bit #b1))(and (= extra_bit_2 #b1)(= extra_bit #b0)))(distinct z_exponent_underflow comp_expo)) ((_ extract 0 0) z_mantissa_underflow_"<<mant_length  + 9<<") null)))" << endl;

    smt2File << "(assert (= s (concat s_help s_last)))" << endl;
    // Zum Runden ist das Guard_bit wichtig, da es dazu dient dass es gerundet wird.
    smt2File << "(assert (= lsb (ite (and (or (and (= extra_bit_2 #b1)(= extra_bit #b1))(and (= extra_bit_2 #b1)(= extra_bit #b0)))(distinct z_exponent_underflow comp_expo)) ((_ extract "<<mantissaWidth + 1<<" "<<mantissaWidth + 1<<") z_mantissa_underflow_"<<mant_length  + 9<<")(ite (and (or (and (= extra_bit_2 #b1)(= extra_bit #b1))(= extra_bit #b0))(= z_exponent_underflow comp_expo)) ((_ extract "<<mantissaWidth  <<" "<<mantissaWidth  <<") z_mantissa_underflow_"<<mant_length  + 9<<") ((_ extract "<<mantissaWidth <<" "<< mantissaWidth<<") z_mantissa_underflow_"<<mant_length  + 9<<")))))" << endl;

    //0101
    //1100
    //1111
    //0111
    //1101
    //0101
    //1101
    //
    //
    //nur Aufrundfälle aufzählen, da beim abrunden, die z_mantisse nicht geändert wird sondern nur gecuttet
    smt2File << "(assert (= z_mantissa_GRS(ite (or (and (= g #b1) (or (= r #b1) (distinct s compare_s)(= add_outshift_number_"<<mant_length + 9 <<" eins))) (and (= g #b1) (= lsb #b1))) (bvadd z_mantissa add_mant) z_mantissa)))" << endl;

    smt2File << "(assert (= z_exponent_over (ite (and (= z_mantissa comp_mant_1) (= z_mantissa_GRS comp_mant_0)) (bvadd z_exponent_underflow add_expo)  z_exponent_underflow)))" << endl;


    smt2File << "(assert (= z_mantissa_NaN (ite (or (and (= x_exponent comp_expo_1) (distinct x_mantissa_extra comp_mant)) (and (= y_exponent comp_expo_1) (distinct y_mantissa_extra comp_mant))) comp_mant_1 z_mantissa_GRS)))" << endl;

    // concat everything and compare with fp
    smt2File << "(assert (= z (concat z_sign z_exponent_over )))" << endl;
    smt2File << "(assert (= z_finale (concat z z_mantissa_NaN)))" << endl;


    // ------------------------------------------------------------------------------------------------------------
    // FP Schreibweise


    if (length_max == 16) {
        smt2File << "(declare-fun x_fp () (_ FloatingPoint 5 11))" << endl; // Single Precision: 8 Bit für den Exponenten, 24 Bit für die Mantisse
        smt2File << "(declare-fun y_fp () (_ FloatingPoint 5 11))" << endl;
        smt2File << "(declare-fun z_fp () (_ FloatingPoint 5 11))" << endl;
    } else if (length_max == 128) {
        smt2File << "(declare-fun x_fp () (_ FloatingPoint 15 113))" << endl; // Single Precision: 8 Bit für den Exponenten, 24 Bit für die Mantisse
        smt2File << "(declare-fun y_fp () (_ FloatingPoint 15 113))" << endl;
        smt2File << "(declare-fun z_fp () (_ FloatingPoint 15 113))" << endl;
    } else if (length_max == 32) {
        // Deklaration von Gleitkommazahlen x, y und z
        smt2File << "(declare-fun x_fp () (_ FloatingPoint 8 24))" << endl; // Single Precision: 8 Bit für den Exponenten, 24 Bit für die Mantisse
        smt2File << "(declare-fun y_fp () (_ FloatingPoint 8 24))" << endl;
        smt2File << "(declare-fun z_fp () (_ FloatingPoint 8 24))" << endl;
    } else if (length_max == 64) {
        smt2File << "(declare-fun x_fp () (_ FloatingPoint 11 53))" << endl; // Single Precision: 8 Bit für den Exponenten, 24 Bit für die Mantisse
        smt2File << "(declare-fun y_fp () (_ FloatingPoint 11 53))" << endl;
        smt2File << "(declare-fun z_fp () (_ FloatingPoint 11 53))" << endl;
    }
    // x = 109999111100000000111100000000110
    // y = 10111111000000000000000000000110

    /*// Setzen von Werten für x und y
    smt2File << "(assert (= x_fp (fp #b0 #b01111111 #b00000000111100000000110)))" << endl; // x = 0.5 (Exponent: 126, Mantisse: 0)
    smt2File << "(assert (= y_fp (fp #b0 #b01111110 #b00111000000000000001111)))" << endl; // y = 0.125 (Exponent: 124, Mantisse: 0)
*/
    smt2File <<"(assert (= true( fp.isNormal x_fp)))"<< endl;
    smt2File <<"(assert (= true( fp.isNormal y_fp)))"<< endl;
    smt2File <<"(assert (= true( fp.isPositive x_fp)))"<< endl;
    smt2File <<"(assert (= true( fp.isPositive y_fp)))"<< endl;
    smt2File <<"(assert (= true( fp.isPositive z_fp)))"<< endl;
    smt2File <<"(assert (= true( fp.isPositive z_fp)))"<< endl;


    // Operationen mit Floating-Point Zahlen (Multiplikation)
    smt2File << "(assert (= z_fp (fp.mul RNE  x_fp y_fp)))" << endl; // Multiplikation von x und y

    if (length_max == 16) {
        // Deklaration von Gleitkommazahlen x, y und z
        smt2File << "(declare-fun x_bv () (_ FloatingPoint 5 11))" << endl;
        smt2File << "(declare-fun y_bv () (_ FloatingPoint 5 11))" << endl;
        smt2File << "(declare-fun z_bv () (_ FloatingPoint 5 11))" << endl;

        smt2File << "(assert (= x_bv ((_ to_fp 5 11) x)))"<< endl;
        smt2File << "(assert (= y_bv ((_ to_fp 5 11) y)))" << endl;
        smt2File << "(assert (= z_bv ((_ to_fp 5 11) z_finale)))" << endl;

        smt2File << "(assert (= x_bv y_fp))" << endl;
        smt2File << "(assert (= y_bv x_fp))" << endl;
        //Verschieden
        smt2File << "(assert (distinct z_bv z_fp))"<< endl;
    } else if (length_max == 128) {
        // Deklaration von Gleitkommazahlen x, y und z
        smt2File << "(declare-fun x_bv () (_ FloatingPoint 15 113))" << endl;
        smt2File << "(declare-fun y_bv () (_ FloatingPoint 15 113))" << endl;
        smt2File << "(declare-fun z_bv () (_ FloatingPoint 15 113))" << endl;

        smt2File << "(assert (= x_bv ((_ to_fp 15 113) x)))"<< endl;
        smt2File << "(assert (= y_bv ((_ to_fp 15 113) y)))" << endl;
        smt2File << "(assert (= z_bv ((_ to_fp 15 113) z_finale)))" << endl;

        smt2File << "(assert (= x_bv y_fp))" << endl;
        smt2File << "(assert (= y_bv x_fp))" << endl;
        //Verschieden
        smt2File << "(assert (distinct z_bv z_fp))"<< endl;
    } else if (length_max == 32) {
        // Deklaration von Gleitkommazahlen x, y und z
        smt2File << "(declare-fun x_bv () (_ FloatingPoint 8 24))" << endl;
        smt2File << "(declare-fun y_bv () (_ FloatingPoint 8 24))" << endl;
        smt2File << "(declare-fun z_bv () (_ FloatingPoint 8 24))" << endl;

        smt2File << "(assert (= x_bv ((_ to_fp 8 24) x)))"<< endl;
        smt2File << "(assert (= y_bv ((_ to_fp 8 24) y)))" << endl;
        smt2File << "(assert (= z_bv ((_ to_fp 8 24) z_finale)))" << endl;

        smt2File << "(assert (= x_bv y_fp))" << endl;
        smt2File << "(assert (= y_bv x_fp))" << endl;
        //Verschieden
        smt2File << "(assert (distinct z_bv z_fp))"<< endl;
    } else if (length_max == 64) {
        // Deklaration von Gleitkommazahlen x, y und z
        smt2File << "(declare-fun x_bv () (_ FloatingPoint 11 53))" << endl;
        smt2File << "(declare-fun y_bv () (_ FloatingPoint 11 53))" << endl;
        smt2File << "(declare-fun z_bv () (_ FloatingPoint 11 53))" << endl;

        smt2File << "(assert (= x_bv ((_ to_fp 11 53) x)))"<< endl;
        smt2File << "(assert (= y_bv ((_ to_fp 11 53) y)))" << endl;
        smt2File << "(assert (= z_bv ((_ to_fp 11 53) z_finale)))" << endl;

        smt2File << "(assert (= x_bv y_fp))" << endl;
        smt2File << "(assert (= y_bv x_fp))" << endl;
        //Verschieden
        smt2File << "(assert (distinct z_bv z_fp))"<< endl;
    }
    //Verschieden
   // smt2File << "(assert (distinct ((_ to_fp 8 24) z_finale) z_fp))"<< endl;

    smt2File << "(check-sat)" << endl;
    smt2File << "(get-model)" << endl;
    smt2File << "(get-value(x y z_finale))" << endl;
    smt2File << "(exit)" << endl;
    smt2File.close();

    cout << signWidth << endl;
    cout << exponentWidth << endl;
    cout << mantissaWidth << endl;
    cout << mant_length << endl;
    cout << length_max << endl;


    cout << "SMT2-Datei erfolgreich erstellt: FP_BV_"+sizebit+"_multiplication.smt2" << endl;
}

