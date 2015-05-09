#include <stdio.h>
#include <assert.h>

#define TRUE 1
#define FALSE 0

// ************* hw-cbmc interface ***********//
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
typedef unsigned __CPROVER_bitvector[1] _u1;


/*
  Module Verilog::top
*/

struct module_top {
  _Bool clk;
  _Bool rst;
  _u8 ser_in;
  _Bool done;
  _u10 xsum_in;
  _u8 xavg_out;
  _u8 xdiff_out;
  _u8 xavg_next;
  _u2 state;
  _u1 once;
};

/*
  Hierarchy Instantiation
*/

extern struct module_top top;

struct state_elements_top {
  _Bool done;
  unsigned int once;
  unsigned short int xsum_in;
  unsigned int state;
  unsigned int xavg_next;
  unsigned int xavg_out;
  unsigned int xdiff_out;
};

struct state_elements_top  stop;

void topc(_Bool clk, _Bool rst, unsigned int ser_in, _Bool *done);

// *********** Implementation in C **************

void topc(_Bool clk, _Bool rst, unsigned int ser_in, _Bool *done)
{
    unsigned int tmp13;
    unsigned int tmp12;
    unsigned int tmp11;
    unsigned int tmp10;
    unsigned int tmp9;
    unsigned int tmp8;
    unsigned int tmp7;
    unsigned short int tmp6;
    unsigned int tmp5;
    unsigned int tmp4;
    unsigned short int tmp3;
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
        tmp3 = (unsigned short int)ser_in;
        tmp4 = 1;
        tmp5 = 1;
        stop.xsum_in = tmp3 & 1023;
        stop.state = tmp4 & 3;
        stop.once = tmp5;
      }

      else
        if(stop.state == 1)
        {
          tmp6 = stop.xsum_in + (unsigned short int)ser_in;
          tmp7 = 0;
          stop.xsum_in = tmp6 & 1023;
          if((_Bool)stop.once)
          {
            tmp8 = 1;
            stop.state = tmp8 & 3;
          }

          else
          {
            tmp9 = 2;
            stop.state = tmp9 & 3;
          }
          stop.once = tmp7; // This update must take place at the end of the current if-else block so as to simulate the effect of reading the old value of stop.once through non-blocking statement
        }

        else
        {
          stop.xavg_next = ((stop.xsum_in + ser_in) >> 2) & 255;
          tmp10 = stop.xavg_next;
          stop.xavg_out = tmp10 & 255;
          if(stop.xavg_next >= ser_in)
          {
            tmp11 = stop.xavg_next - ser_in;
            stop.xdiff_out = tmp11 & 255;
          }

          else
          {
            tmp12 = ser_in - stop.xavg_next;
            stop.xdiff_out = tmp12 & 255;
          }
          tmp13 = 0;
          stop.state = tmp13 & 3;
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
  // because that is when the xavg_out and xavg_di  // ff is computed
  assert(stop.xavg_out==top.xavg_out);
  assert(stop.xdiff_out==top.xdiff_out);
  assert(stop.state==top.state);

  // Again a new cycle begins from state 0

  top.rst=0;
  top.ser_in=10;
  set_inputs();
  next_timeframe();
  topc(clk, 0, 10, &stop.done);
  assert(stop.xavg_out==top.xavg_out);
  assert(stop.xdiff_out==top.xdiff_out);
  assert(stop.state==top.state);

  top.rst=0;
  top.ser_in=20;
  set_inputs();
  next_timeframe();
  topc(clk, 0, 20, &stop.done);
  assert(stop.xavg_out==top.xavg_out);
  assert(stop.xdiff_out==top.xdiff_out);
  assert(stop.state==top.state);

  top.rst=0;
  top.ser_in=30;
  set_inputs();
  next_timeframe();
  topc(clk, 0, 30, &stop.done);
  assert(stop.xavg_out==top.xavg_out);
  assert(stop.xdiff_out==top.xdiff_out);
  assert(stop.state==top.state);

  top.rst=0;
  top.ser_in=40;
  set_inputs();
  next_timeframe();
  topc(clk, 0, 40, &stop.done);
  assert(stop.xavg_out==top.xavg_out);
  assert(stop.xdiff_out==top.xdiff_out);
  assert(stop.state==top.state);
  // 2nd cycle ends here

  top.rst=0;
  top.ser_in=4;
  set_inputs();
  next_timeframe();
  topc(clk, 0, 4, &stop.done);
  assert(stop.xavg_out==top.xavg_out);
  assert(stop.xdiff_out==top.xdiff_out);
  assert(stop.state==top.state);
}


