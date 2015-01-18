#include <assert.h>
#include <stdio.h>
#define TRUE 1
#define FALSE 0

/* Unwinding Bound */

extern const unsigned int bound;

/* Next Timeframe  */

void next_timeframe(void);
void set_inputs(void);


/*
  Type declarations
*/

typedef unsigned int _u32;
typedef unsigned __CPROVER_bitvector[4] _u4;
typedef unsigned __CPROVER_bitvector[9] _u9;
typedef unsigned char _u8;
typedef unsigned __CPROVER_bitvector[19] _u19;



/*
  Module Verilog::fir_fsm
*/

struct module_fir_fsm {
  _Bool clock;
  _Bool reset;
  _Bool in_valid;
  _u32 state_out;
  _u4 state;
  _u32 state_tmp;
};


/*
  Module Verilog::fir_data
*/

struct module_fir_data {
  _u32 state_out;
  _Bool reset;
  _u32 sample;
  _u32 result;
  _Bool output_data_ready;
  _u9 coefs0;
  _u9 coefs1;
  _u9 coefs2;
  _u9 coefs3;
  _u9 coefs4;
  _u9 coefs5;
  _u9 coefs6;
  _u9 coefs7;
  _u9 coefs8;
  _u9 coefs9;
  _u9 coefs10;
  _u9 coefs11;
  _u9 coefs12;
  _u9 coefs13;
  _u9 coefs14;
  _u9 coefs15;
  _u8 sample_tmp;
  _u19 acc;
  _u8 shift0;
  _u8 shift1;
  _u8 shift2;
  _u8 shift3;
  _u8 shift4;
  _u8 shift5;
  _u8 shift6;
  _u8 shift7;
  _u8 shift8;
  _u8 shift9;
  _u8 shift10;
  _u8 shift11;
  _u8 shift12;
  _u8 shift13;
  _u8 shift14;
  _u8 shift15;
  _u32 state;
  _u8 sample_tmp_0;
  _u19 acc_1;
  _u19 acc_2;
  _u19 acc_3;
  _u19 acc_4;
  _u19 acc_5;
  _u19 acc_6;
  _u19 acc_7;
  _u19 acc_8;
  _u19 acc_9;
  _u19 acc_10;
  _u19 acc_11;
  _u19 acc_12;
  _u19 acc_13;
  _u19 acc_14;
  _u19 acc_15;
  _u19 acc_16;
  _u8 shift15_17;
  _u8 shift14_18;
  _u8 shift13_19;
  _u8 shift12_20;
  _u8 shift11_21;
  _u8 shift10_22;
  _u8 shift9_23;
  _u8 shift8_24;
  _u8 shift7_25;
  _u8 shift6_26;
  _u8 shift5_27;
  _u8 shift4_28;
  _u8 shift3_29;
  _u8 shift2_30;
  _u8 shift1_31;
  _u8 shift0_32;
  _u32 result_33;
};

/*
  Module Verilog::top
*/

struct module_top {
  _u32 SAMPLE;
  _Bool IN_VALID;
  _Bool RESET;
  _Bool CLK;
  _Bool OUTPUT_DATA_READY;
  _u32 RESULT;
  _u32 state_out;
  _u32 result_ins;
  _Bool output_data_ready_ins;
  struct module_fir_fsm fir_fsm1;
  struct module_fir_data fir_data1;
};




/*
  Hierarchy Instantiation
*/

extern struct module_top top;

// ************** Implementation in C ***********
/*struct state_elements_fir_fsm{
  unsigned int state_out;
  unsigned int state_tmp;
  unsigned char state;
};

struct state_elements_fir_fsm  sfir_fsm;
void fir_fsm(_Bool clock, _Bool reset, _Bool in_valid, unsigned int *state_out)
{
  unsigned char tmp0;
  if((unsigned char)reset == 1)
  {
    tmp0 = 0;
  }

  else
  {
      if(sfir_fsm.state == 0)
      {
        sfir_fsm.state = 1;
        sfir_fsm.state_tmp = 0;
        sfir_fsm.state_out = sfir_fsm.state_tmp & 4294967295;
        *state_out = sfir_fsm.state_tmp & 4294967295;
      }

      else
        if(sfir_fsm.state == 1)
        {
          if((unsigned int)in_valid == 1)
          {
            sfir_fsm.state = 2;
          }

          sfir_fsm.state_tmp = 1;
          sfir_fsm.state_out = sfir_fsm.state_tmp & 4294967295;
          *state_out = sfir_fsm.state_tmp & 4294967295;
        }

        else
          if(sfir_fsm.state == 2)
          {
            sfir_fsm.state = 3;
            sfir_fsm.state_tmp = 2;
            sfir_fsm.state_out = sfir_fsm.state_tmp & 4294967295;
            *state_out = sfir_fsm.state_tmp & 4294967295;
          }

          else
            if(sfir_fsm.state == 3)
            {
              sfir_fsm.state = 4;
              sfir_fsm.state_tmp = 3;
              sfir_fsm.state_out = sfir_fsm.state_tmp & 4294967295;
              *state_out = sfir_fsm.state_tmp & 4294967295;
            }

            else
              if(TRUE)
              {
                sfir_fsm.state = 1;
                sfir_fsm.state_tmp = 4;
                sfir_fsm.state_out = sfir_fsm.state_tmp & 4294967295;
                *state_out = sfir_fsm.state_tmp & 4294967295;
              }
  }
  if((unsigned char)reset == 1)
  {
    sfir_fsm.state = tmp0 & 15;
  }
}

struct state_elements_fir_data {
  _Bool output_data_ready;
  unsigned int acc;
  unsigned int result;
  unsigned int state;
  unsigned char sample_tmp;
  unsigned char shift0;
  unsigned char shift1;
  unsigned char shift10;
  unsigned char shift11;
  unsigned char shift12;
  unsigned char shift13;
  unsigned char shift14;
  unsigned char shift15;
  unsigned char shift2;
  unsigned char shift3;
  unsigned char shift4;
  unsigned char shift5;
  unsigned char shift6;
  unsigned char shift7;
  unsigned char shift8;
  unsigned char shift9;
};

struct state_elements_fir_data  sfir_data;
void fir_data(_Bool reset, unsigned int state_out, unsigned int sample, unsigned int *result, _Bool *output_data_ready)
{
  unsigned short int coefs0;
  unsigned short int coefs1;
  unsigned short int coefs2;
  unsigned short int coefs3;
  unsigned short int coefs4;
  unsigned short int coefs5;
  unsigned short int coefs6;
  unsigned short int coefs7;
  unsigned short int coefs8;
  unsigned short int coefs9;
  unsigned short int coefs10;
  unsigned short int coefs11;
  unsigned short int coefs12;
  unsigned short int coefs13;
  unsigned short int coefs14;
  unsigned short int coefs15;
  int i;
  coefs0 = -6;
  coefs1 = -4;
  coefs2 = 13;
  coefs3 = 16;
  coefs4 = -18;
  coefs5 = -41;
  coefs6 = 23;
  coefs7 = 154;
  coefs8 = 222;
  coefs9 = 154;
  coefs10 = 23;
  coefs11 = -41;
  coefs12 = -18;
  coefs13 = 16;
  coefs14 = 13;
  coefs15 = -4;
  if((unsigned char)reset == 1)
  {
    sfir_data.sample_tmp = 0;
    sfir_data.acc = 0;
    sfir_data.shift0 = 0;
    sfir_data.shift1 = 0;
    sfir_data.shift2 = 0;
    sfir_data.shift3 = 0;
    sfir_data.shift4 = 0;
    sfir_data.shift5 = 0;
    sfir_data.shift6 = 0;
    sfir_data.shift7 = 0;
    sfir_data.shift8 = 0;
    sfir_data.shift9 = 0;
    sfir_data.shift10 = 0;
    sfir_data.shift11 = 0;
    sfir_data.shift12 = 0;
    sfir_data.shift13 = 0;
    sfir_data.shift14 = 0;
    sfir_data.shift15 = 0;
  }
  sfir_data.result = 0;
	*result=0;
  sfir_data.output_data_ready = FALSE;
  *output_data_ready = FALSE;
  sfir_data.state = state_out & 4294967295;
    if(sfir_data.state == 1)
    {
      sfir_data.sample_tmp = (unsigned char)sample & 255;
      sfir_data.acc = (unsigned int)(unsigned short int)sfir_data.sample_tmp * (unsigned int)coefs0 & 524287;
      sfir_data.acc = sfir_data.acc + (unsigned int)(unsigned short int)sfir_data.shift14 * (unsigned int)coefs15 & 524287;
      sfir_data.acc = sfir_data.acc + (unsigned int)(unsigned short int)sfir_data.shift13 * (unsigned int)coefs14 & 524287;
      sfir_data.acc = sfir_data.acc + (unsigned int)(unsigned short int)sfir_data.shift12 * (unsigned int)coefs13 & 524287;
      sfir_data.acc = sfir_data.acc + (unsigned int)(unsigned short int)sfir_data.shift11 * (unsigned int)coefs12 & 524287;
    }

    else
      if(sfir_data.state == 2)
      {
        sfir_data.acc = sfir_data.acc + (unsigned int)(unsigned short int)sfir_data.shift10 * (unsigned int)coefs11 & 524287;
        sfir_data.acc = sfir_data.acc + (unsigned int)(unsigned short int)sfir_data.shift9 * (unsigned int)coefs10 & 524287;
        sfir_data.acc = sfir_data.acc + (unsigned int)(unsigned short int)sfir_data.shift8 * (unsigned int)coefs9 & 524287;
        sfir_data.acc = sfir_data.acc + (unsigned int)(unsigned short int)sfir_data.shift7 * (unsigned int)coefs8 & 524287;
      }

      else
        if(sfir_data.state == 3)
        {
          sfir_data.acc = sfir_data.acc + (unsigned int)(unsigned short int)sfir_data.shift6 * (unsigned int)coefs7 & 524287;
          sfir_data.acc = sfir_data.acc + (unsigned int)(unsigned short int)sfir_data.shift5 * (unsigned int)coefs6 & 524287;
          sfir_data.acc = sfir_data.acc + (unsigned int)(unsigned short int)sfir_data.shift4 * (unsigned int)coefs5 & 524287;
          sfir_data.acc = sfir_data.acc + (unsigned int)(unsigned short int)sfir_data.shift3 * (unsigned int)coefs4 & 524287;
        }

        else
          if(sfir_data.state == 4)
          {
            sfir_data.acc = sfir_data.acc + (unsigned int)(unsigned short int)sfir_data.shift2 * (unsigned int)coefs3 & 524287;
            sfir_data.acc = sfir_data.acc + (unsigned int)(unsigned short int)sfir_data.shift1 * (unsigned int)coefs2 & 524287;
            sfir_data.acc = sfir_data.acc + (unsigned int)(unsigned short int)sfir_data.shift0 * (unsigned int)coefs1 & 524287;
            sfir_data.shift15 = sfir_data.shift14 & 255;
            sfir_data.shift14 = sfir_data.shift13 & 255;
            sfir_data.shift13 = sfir_data.shift12 & 255;
            sfir_data.shift12 = sfir_data.shift11 & 255;
            sfir_data.shift11 = sfir_data.shift10 & 255;
            sfir_data.shift10 = sfir_data.shift9 & 255;
            sfir_data.shift9 = sfir_data.shift8 & 255;
            sfir_data.shift8 = sfir_data.shift7 & 255;
            sfir_data.shift7 = sfir_data.shift6 & 255;
            sfir_data.shift6 = sfir_data.shift5 & 255;
            sfir_data.shift5 = sfir_data.shift4 & 255;
            sfir_data.shift4 = sfir_data.shift3 & 255;
            sfir_data.shift3 = sfir_data.shift2 & 255;
            sfir_data.shift2 = sfir_data.shift1 & 255;
            sfir_data.shift1 = sfir_data.shift0 & 255;
            sfir_data.shift0 = (unsigned char)sample & 255;
            sfir_data.result = (unsigned int)sfir_data.acc & 4294967295;
            *result = (unsigned int)sfir_data.acc & 4294967295;
            sfir_data.output_data_ready = TRUE;
            *output_data_ready = TRUE;
          }

}
struct state_elements_fir {
  _Bool OUTPUT_DATA_READY;
  unsigned int RESULT;
  struct state_elements_fir_fsm fir_fsm1;
	struct state_elements_fir_data fir_data1;
};

void top1(unsigned int SAMPLE, _Bool IN_VALID, _Bool RESET, _Bool CLK, _Bool *OUTPUT_DATA_READY, unsigned int *RESULT)
{
  struct state_elements_fir  sfir;
  unsigned int state_out;
  unsigned int result_ins;
  _Bool output_data_ready_ins;
  fir_fsm(CLK, RESET, IN_VALID, &state_out);
  fir_data(RESET, state_out, SAMPLE, &result_ins, &output_data_ready_ins);
  sfir.RESULT = result_ins & 4294967295;
  *RESULT = result_ins & 4294967295;
  sfir.OUTPUT_DATA_READY = output_data_ready_ins;
  *OUTPUT_DATA_READY = output_data_ready_ins;
}*/
// **********************************************

void main()
{
	top.RESET = 1;
	top.IN_VALID = 0;
	set_inputs();
	next_timeframe();
	//assert(top.RESULT == 0);
  //assert(top.OUTPUT_DATA_READY == 0);
	
	top.RESET = 0;
	top.IN_VALID = 1;
	top.SAMPLE = 23;
	set_inputs();
	next_timeframe();
	assert(top.RESULT == 0);
  assert(top.OUTPUT_DATA_READY == 0);
	
	top.RESET = 0;
	top.IN_VALID = 1;
	top.SAMPLE = 32;
	set_inputs();
	next_timeframe();
	assert(top.RESULT == 0);
  assert(top.OUTPUT_DATA_READY == 0);


	top.RESET = 0;
	top.IN_VALID = 1;
	top.SAMPLE = 54;
	set_inputs();
	next_timeframe();
	assert(top.RESULT == 0);
  assert(top.OUTPUT_DATA_READY == 0);
	
	top.RESET = 0;
	top.IN_VALID = 1;
	top.SAMPLE = 54;
	set_inputs();
	next_timeframe();
	assert(top.RESULT == 0);
  assert(top.OUTPUT_DATA_READY == 0);
	
	top.RESET = 0;
	top.IN_VALID = 1;
	top.SAMPLE = 54;
	set_inputs();
	next_timeframe();
	assert(top.RESULT == 0);
  assert(top.OUTPUT_DATA_READY == 0);
	
	top.RESET = 0;
	top.IN_VALID = 1;
	top.SAMPLE = 24;
	set_inputs();
	next_timeframe();
	assert(top.RESULT == 0);
  assert(top.OUTPUT_DATA_READY != 0);
  //assert(top.OUTPUT_DATA_READY != 0);
	
	top.RESET = 0;
	top.IN_VALID = 1;
	top.SAMPLE = 24;
	set_inputs();
	next_timeframe();
	assert(top.RESULT == 0);
  assert(top.OUTPUT_DATA_READY != 0);
	
	top.RESET = 0;
	top.IN_VALID = 1;
	top.SAMPLE = 54;
	set_inputs();
	next_timeframe();
	assert(top.RESULT != 0);
  assert(top.OUTPUT_DATA_READY != 0);
	
	top.RESET = 0;
	top.IN_VALID = 1;
	top.SAMPLE = 54;
	set_inputs();
	next_timeframe();
	assert(top.RESULT != 0);
  assert(top.OUTPUT_DATA_READY != 0);

	top.RESET = 0;
	top.IN_VALID = 1;
	top.SAMPLE = 54;
	set_inputs();
	next_timeframe();
	assert(top.RESULT != 0);
  assert(top.OUTPUT_DATA_READY != 0);


	top.RESET = 0;
	top.IN_VALID = 1;
	top.SAMPLE = 54;
	set_inputs();
	next_timeframe();
	assert(top.RESULT != 0);
  assert(top.OUTPUT_DATA_READY != 0);

	top.RESET = 0;
	top.IN_VALID = 1;
	top.SAMPLE = 54;
	set_inputs();
	next_timeframe();
	assert(top.RESULT != 0);
  assert(top.OUTPUT_DATA_READY != 0);

	top.RESET = 0;
	top.IN_VALID = 1;
	top.SAMPLE = 54;
	set_inputs();
	next_timeframe();
	assert(top.RESULT != 0);
  assert(top.OUTPUT_DATA_READY != 0);

	top.RESET = 0;
	top.IN_VALID = 1;
	top.SAMPLE = 54;
	set_inputs();
	next_timeframe();
	assert(top.RESULT != 0);
  assert(top.OUTPUT_DATA_READY != 0);
	
	top.RESET = 0;
	top.IN_VALID = 1;
	top.SAMPLE = 54;
	set_inputs();
	next_timeframe();
	assert(top.RESULT != 0);
  assert(top.OUTPUT_DATA_READY != 0);
}


