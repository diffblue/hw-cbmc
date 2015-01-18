#include <stdio.h>
#include<assert.h>
#define TRUE 1
#define FALSE 0

// *********** HW-CBMC Interface ****************** //
/* Unwinding Bound */

extern const unsigned int bound;

/* Next Timeframe  */

void next_timeframe(void);
void set_inputs(void);


/*
  Type declarations
*/

typedef unsigned char _u8;
typedef unsigned __CPROVER_bitvector[10] _u10;
typedef unsigned __CPROVER_bitvector[2] _u2;


/*
  Module Verilog::top
*/

struct module_top {
  _Bool clk;
  _Bool rst;
  _u8 ser_in;
  _Bool done;
  _u8 s0_in;
  _u8 s1_in;
  _u8 s2_in;
  _u10 xsum1_in;
  _u10 xsum2_in;
  _u8 xavg_out;
  _u8 xdiff_out;
  _u8 xavg_next;
  _u2 state;
  _u10 xsum1_in_0;
  _u10 xsum2_in_1;
  _u8 xavg_next_2;
  _u8 xdiff_out_3;
  _u8 xdiff_out_4;
  _Bool done_5;
};




/*
  Hierarchy Instantiation
*/

extern struct module_top top;

struct state_elements_top{
  _Bool done;
  unsigned int xsum1_in;
  unsigned int xsum2_in;
  unsigned int state;
  unsigned int s0_in;
  unsigned int s1_in;
  unsigned int s2_in;
  unsigned int xavg_next;
  unsigned int xavg_out;
  unsigned int xdiff_out;
};
struct state_elements_top  stop;

void topc(_Bool clk, _Bool rst, unsigned int ser_in, _Bool *done);

// ******** C Implementation of Adder *************//


void topc(_Bool clk, _Bool rst, unsigned int ser_in, _Bool *done)
{
    unsigned int tmp40;
    unsigned int tmp30;
    unsigned int tmp11;
    unsigned int tmp10;
    unsigned int tmp9;
    unsigned int tmp8;
    unsigned int tmp7;
    unsigned int tmp6;
    unsigned int tmp5;
    unsigned int tmp4;
    unsigned int tmp3;
    unsigned int tmp2;
    unsigned int tmp1;
    unsigned int tmp0;
    if(rst)
    {
      tmp0 = 0;
      tmp1 = 0;
      tmp2 = 0;
      stop.xavg_out = tmp0 & 255;
      stop.xdiff_out = tmp1 & 255;
      stop.state = tmp2 & 3;
    }

    else
    {
      if(stop.state == 0)
      {
        tmp3 = ser_in;
        tmp4 = 1;
        stop.s0_in = tmp3 & 255;
        stop.state = tmp4 & 3;
      }

      else
        if(stop.state == 1)
        {
          tmp5 = ser_in;
          tmp30 = 2;
          stop.s1_in = tmp5 & 255;
          stop.state = tmp30 & 3;

        }

        else
          if(stop.state == 2)
          {
            tmp6 = ser_in;
            tmp7 = stop.s0_in + stop.s1_in;
            tmp40 = 3;
            stop.s2_in = tmp6 & 255;
            stop.xsum1_in = tmp7 & 1023;
            stop.state = tmp40 & 3;
          }

          else
          {
            stop.xsum2_in = (ser_in + stop.s2_in) & 1023;
            stop.xavg_next = ((stop.xsum1_in + stop.xsum2_in) >> 2) & 255;
            tmp8 = stop.xavg_next;
            stop.xavg_out = tmp8 & 255;
            if(stop.xavg_next >= ser_in)
            {
              tmp9 = stop.xavg_next - ser_in;
              stop.xdiff_out = tmp9 & 255;
            }

            else
            {
              tmp10 = ser_in - stop.xavg_next;
              stop.xdiff_out = tmp10 & 255;
            }
            tmp11 = 0;
            stop.state = tmp11 & 3;
          }
    }
  
    stop.done = (stop.state == 0);
}

void main()
{
  _Bool clk;
  _Bool rst;
  unsigned int ser_in;

  top.rst=1;
  set_inputs();
  next_timeframe();
  topc(clk, 1, ser_in, &stop.done);

  assert(stop.xavg_out==top.xavg_out);
  assert(stop.xdiff_out==top.xdiff_out);
  assert(stop.state==top.state);

  top.rst=0;
  top.ser_in=2;
  set_inputs();
  next_timeframe();
  topc(clk, 0, 2, &stop.done);
  assert(stop.xavg_out==top.xavg_out);
  assert(stop.xdiff_out==top.xdiff_out);
  assert(stop.state==top.state);

  top.rst=0;
  top.ser_in=3;
  set_inputs();
  next_timeframe();
  topc(clk, 0, 3, &stop.done);
  assert(stop.xavg_out==top.xavg_out);
  assert(stop.xdiff_out==top.xdiff_out);
  assert(stop.state==top.state);

  top.rst=0;
  top.ser_in=4;
  set_inputs();
  next_timeframe();
  topc(clk, 0, 4, &stop.done);
  assert(stop.xavg_out==top.xavg_out);
  assert(stop.xdiff_out==top.xdiff_out);
  assert(stop.state==top.state);

  top.rst=0;
  top.ser_in=5;
  set_inputs();
  next_timeframe();
  topc(clk, 0, 5, &stop.done);
  
  // The following two assertion makes sense
  // only after the end of 4th cycle when state==3
  // because that is when the xavg_out and xavg_diff is computed
  assert(stop.xavg_out==top.xavg_out);
  assert(stop.xdiff_out==top.xdiff_out);
  assert(stop.state==top.state);

  // Again a new cycle begins from state 0

  top.rst=0;
  top.ser_in=1;
  set_inputs();
  next_timeframe();
  topc(clk, 0, 1, &stop.done);
  assert(stop.xavg_out==top.xavg_out);
  assert(stop.xdiff_out==top.xdiff_out);
  assert(stop.state==top.state);

  top.rst=0;
  top.ser_in=2;
  set_inputs();
  next_timeframe();
  topc(clk, 0, 2, &stop.done);
  assert(stop.xavg_out==top.xavg_out);
  assert(stop.xdiff_out==top.xdiff_out);
  assert(stop.state==top.state);
  //assert(top.state[0]==1);

  top.rst=0;
  top.ser_in=3;
  set_inputs();
  next_timeframe();
  topc(clk, 0, 3, &stop.done);
  assert(stop.xavg_out==top.xavg_out);
  assert(stop.xdiff_out==top.xdiff_out);
  assert(stop.state==top.state);

  top.rst=0;
  top.ser_in=4;
  set_inputs();
  next_timeframe();
  topc(clk, 0, 4, &stop.done);
  assert(stop.xavg_out==top.xavg_out);
  assert(stop.xdiff_out==top.xdiff_out);
  assert(stop.state==top.state);
  // 2nd cycle ends here
}


