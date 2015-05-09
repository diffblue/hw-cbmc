#include <stdio.h>
#define TRUE 1
#define FALSE 0


// ******** hw-cbmc interface ***********//

/* Unwinding Bound */

extern const unsigned int bound;

/* Next Timeframe  */

void next_timeframe(void);
void set_inputs(void);


/*
  Type declarations
*/

typedef unsigned __CPROVER_bitvector[5] _u5;
typedef unsigned __CPROVER_bitvector[4] _u4;


/*
  Module Verilog::top
*/

struct module_top {
  _Bool clk_i;
  _u5 dat_bcd_i;
  _u4 dat_bin_o;
  _u4 dat_gray_o;
  _u4 tens_digit;
  _u4 no_tens_digit;
  _Bool tens_select;
};

/*
  Hierarchy Instantiation
*/

extern struct module_top top;

// ********** Implementation in C **********//

struct state_elements_bcd_to_binary {
  _Bool tens_select;
  unsigned char dat_bin_o;
  unsigned char dat_gray_o;
  unsigned char no_tens_digit;
  unsigned char tens_digit;
};

struct state_elements_bcd_to_binary sbcd_to_binary;

void topc(_Bool clk_i, unsigned char dat_bcd_i, unsigned char *dat_bin_o, unsigned char *dat_gray_o)
{
  unsigned char tmp5;
  unsigned char tmp4;
  unsigned char tmp3;
  _Bool tmp2;
  unsigned char tmp1;
  unsigned char tmp0;
  tmp0 = (dat_bcd_i & 0x0F) + 0xA;
  tmp1 = dat_bcd_i & 15;
  tmp2 = dat_bcd_i >> 4 & 1;
  if(sbcd_to_binary.tens_select)
    tmp3 = sbcd_to_binary.tens_digit;

  else
    tmp4 = sbcd_to_binary.no_tens_digit;
  
  tmp5 = (((*dat_bin_o >> 3) & 0x1) << 3) | ((((*dat_bin_o >> 3 & 0x1) ^ (*dat_bin_o >> 2 & 0x1)) & 0x1) << 2) |
         ((((*dat_bin_o >> 2 & 0x1) ^ (*dat_bin_o >> 1 & 0x1)) & 0x1) << 1) | (((*dat_bin_o >> 1 & 0x1) ^ (*dat_bin_o & 0x1)) & 0x1);

  sbcd_to_binary.tens_digit = tmp0 & 15;
  sbcd_to_binary.no_tens_digit = tmp1 & 15;
  sbcd_to_binary.tens_select = tmp2;
  
  if(sbcd_to_binary.tens_select) {
    sbcd_to_binary.dat_bin_o = tmp3 & 15;
    *dat_bin_o = tmp3 & 15;
  }
  else {
    sbcd_to_binary.dat_bin_o = tmp4 & 15;
    *dat_bin_o = tmp4 & 15;
  }

  sbcd_to_binary.dat_gray_o = tmp5 & 15;
  *dat_gray_o = tmp5 & 15;
}


// ************** harness ****************//

void main()
{
  _Bool clk_i;
  unsigned char dat_bin_o; 
  unsigned char dat_gray_o;
  
  top.dat_bcd_i = 5;
  set_inputs();
  next_timeframe();
  topc(clk_i, 5, &dat_bin_o, &dat_gray_o);
  assert(dat_bin_o == 0);

  top.dat_bcd_i = 19;
  set_inputs();
  next_timeframe();
  topc(clk_i, 19, &dat_bin_o, &dat_gray_o);
  
  top.dat_bcd_i = 21;
  set_inputs();
  next_timeframe();
  topc(clk_i, 21, &dat_bin_o, &dat_gray_o);
  assert(top.dat_bin_o == dat_bin_o);
  assert(dat_bin_o == 13);
  
  top.dat_bcd_i = 29;
  set_inputs();
  next_timeframe();
  topc(clk_i, 29, &dat_bin_o, &dat_gray_o);
  assert(top.dat_bin_o == dat_bin_o);
  assert(dat_bin_o == 15);
}
