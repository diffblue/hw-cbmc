#include <stdio.h>
#define TRUE 1
#define FALSE 0

// ********* hw-cbmc interface ***********//

/* Unwinding Bound */

extern const unsigned int bound;

/* Next Timeframe  */

void next_timeframe(void);
void set_inputs(void);


/*
  Type declarations
*/

typedef unsigned __CPROVER_bitvector[3] _u3;


/*
  Module Verilog::top
*/

struct module_top {
  _Bool clock;
  _Bool reset;
  _Bool line1;
  _Bool line2;
  _Bool outp;
  _Bool overflw;
  _u3 stato;
  _Bool outp_0;
  _Bool outp_1;
  _Bool outp_2;
  _Bool outp_3;
  _Bool outp_4;
  _Bool outp_5;
  _Bool outp_6;
  _Bool outp_7;
};




/*
  Hierarchy Instantiation
*/

extern struct module_top top;

// ********** implementation in C *********//

struct state_elements_fsm {
  _Bool outp;
  _Bool overflw;
  unsigned char stato;
};
struct state_elements_fsm  sfsm;

void topc(_Bool clock, _Bool reset, _Bool line1, _Bool line2, _Bool *outp, _Bool *overflw)
{
  if((unsigned char)reset == 1)
  {
    sfsm.stato = 0;
    sfsm.outp = FALSE;
    sfsm.overflw = FALSE;
		*outp = FALSE;
		*overflw = FALSE;
  }

  else
  {
      if(sfsm.stato == 0)
      {
        if((unsigned char)line1 == 1 && (unsigned char)line2 == 1)
          sfsm.stato = 4;

        else
          sfsm.stato = 1;
          sfsm.outp = line1 ^ line2;
          sfsm.overflw = FALSE;
		      *outp = line1 ^ line2;
		      *overflw = FALSE;
      }

      else
        if(sfsm.stato == 3)
        {
          if((unsigned char)line1 == 1 && (unsigned char)line2 == 1)
            sfsm.stato = 4;

          else
            sfsm.stato = 1;
            sfsm.outp = line1 ^ line2;
            sfsm.overflw = TRUE;
		        *outp = line1 ^ line2;
		        *overflw = TRUE;
        }

        else
          if(sfsm.stato == 1)
          {
            if((unsigned char)line1 == 1 && (unsigned char)line2 == 1)
              sfsm.stato = 5;

            else
              sfsm.stato = 2;
              sfsm.outp = line1 ^ line2;
              sfsm.overflw = FALSE;
		          *outp = line1 ^ line2;
		          *overflw = FALSE;
          }

          else
            if(sfsm.stato == 4)
            {
              if((unsigned char)line1 == 1 && (unsigned char)line2 == 1)
                sfsm.stato = 5;

              else
                sfsm.stato = 2;
                sfsm.outp = !(line1 ^ line2);
                sfsm.overflw = FALSE;
		            *outp = !(line1 ^ line2);
		            *overflw = FALSE;
            }

            else
              if(sfsm.stato == 2)
              {
                if((unsigned char)line1 == 1 && (unsigned char)line2 == 1)
                  sfsm.stato = 7;

                else
                  sfsm.stato = 6;
                  sfsm.outp = line1 ^ line2;
                  sfsm.overflw = FALSE;
		              *outp = line1 ^ line2;
		              *overflw = FALSE;
              }

              else
                if(sfsm.stato == 5)
                {
                  if((unsigned char)line1 == 1 && (unsigned char)line2 == 1)
                    sfsm.stato = 7;

                  else
                    sfsm.stato = 6;
                    sfsm.outp = !(line1 ^ line2);
                    sfsm.overflw = FALSE;
		                *outp = !(line1 ^ line2);
		                *overflw = FALSE;
                }

                else
                  if(sfsm.stato == 6)
                  {
                    if((unsigned char)line1 == 1 && (unsigned char)line2 == 1)
                      sfsm.stato = 3;

                    else
                      sfsm.stato = 0;
                      sfsm.outp = line1 ^ line2;
                      sfsm.overflw = FALSE;
		                  *outp = line1 ^ line2;
		                  *overflw = FALSE;
                  }

                  else
                    if(sfsm.stato == 7)
                    {
                      if((unsigned char)line1 == 1 && (unsigned char)line2 == 1)
                        sfsm.stato = 3;

                      else
                        sfsm.stato = 0;
                        sfsm.outp = !(line1 ^ line2);
                        sfsm.overflw = FALSE;
		                    *outp = !(line1 ^ line2);
		                    *overflw = FALSE;
                    }

  }
}

void main()
{
	_Bool clk, outp, overflw;
	top.reset=1;
	top.line1=1;
	top.line2=0;
	set_inputs();
	next_timeframe();
	topc(clk,1,1,0,&outp,&overflw);
	assert(top.outp == outp);


	top.reset=0;
	top.line1=1;
	top.line2=1;
	set_inputs();
	next_timeframe();
	topc(clk,0,1,1,&outp,&overflw);
	assert(top.outp == outp);
}
