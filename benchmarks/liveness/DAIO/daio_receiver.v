/*
*  Author:	Rajesh Gupta
*  Revised:	1990-05-24
*  Comment:	Based on daio_receiver.hc by Thomas Truong
*  Comment:	Translation into Verilog and probable addition
*               of bugs by Fabio Somenzi 
*/

/*

	This benchmark is a description of the receiver section used
in the Digital Audio Input-Output chip (DAIO). A detailed description
of this chip can be found in:

	M. M. Ligthard, A. Bechtolsheim, G. D. Micheli, A. El Gamal
	``Design of a Digital Input Output Chip'', Custom IC Conference,
	May 1989.


BRIEF DESCRIPTION:
	
	DAIO facilitates transfer of data between a personal computer
and a CD or DAT player. DAIO is a full duplex, fully symmetrical interface
chip for the reception and transmission of digital audio signals. Receive
in this context is defined as the data flow from the digial audio device
to the uP bus and transmit is defined as the data flow the other way around.
 
	DAIO divided into two parts: a receive section
which transfers data from a CD player to the PC and a transmit section
which sends data from a PC to a CD recoder (or other recorder that 
adheres to the AES protocol). The receive section consists of two
parts:
	
	phase decoder: its main functions are -
		- detect start of the digital audio transmission
		- synchronize the bit-clock to match the data rate
		- decode the data and transmit it to the receive
		  	register and buffer
	
	The phase decoder waits for a transition inthe biphase signal
	and starts looking for a 'start of block' preamble. The preambles
	and actual bit values are extracted from the biphase signal by 
	means of counting samples in a ten bits wide window. 

	receiver: (this description)

	briefly, this portion shifts in extracted bits in to a 20-bit
	register. After a frame is assembled the receiver signal the
	host to read the register by raising 'load' signals. 


*  Main Process daio_receiver() 
*
*  Inputs:
*      xtal[0:3]		: clocks.
*      rx_control[0:3]      	: control inputs.
*				   [0:1]  - clock select
*				    [2]   - receiver enable
*			            [3]   - parity enable
*      reset        		: global reset.
*      bit_in       		: extracted bit value from biphase signal.
*      preamble_1     		: start of block.
*      preamble_2	        : start of subframe_A.
*      preamble_3		: start of subframe_B.
*      carrier_loss 		: too many violations --> lost carrier.
*      biphase_violation	: no transition between bits.
* Outputs:
*      clock_out		: clock selected from xtal[0:3].
*      rx_status[0:3] 		: status outputs.
*				   [0] - carrier_loss
*			  	   [1] - biphase_violation
*			  	   [2] - sync_problem
*				   [3] - parity_error
*      parity			: parity of current subframe.
*      load_A       		: parallel load of subframe_A from shift_reg.
*      load_B       		: parallel load of subframe_B from shift_reg.
*      load_buff     		: paralell load of register_bank into buffer.
*	shift_reg		: storage of last 20 bits from phase_decoder.
*      frame_ofs		: last 2 bits of frame counter.
*
*/

//typedef enum {L0, L1, L2, L3, L4, L5, L6, L7, L8, L9, L10} states;

module daio_receiver(clock,
                     xtal,rx_control,reset,bit_in,
		     preamble_1,preamble_2,preamble_3,
		     carrier_loss,biphase_violation,
	 	     clock_out,rx_status,parity,load_A,load_B,load_buff,
		     shift_reg,frame_ofs);
    input clock;
    input [3:0]   xtal;			// clocks
    input [3:0]   rx_control;		// control inputs
    input 	  reset;		// global reset
    input 	  bit_in;		// extracted bit from biphase
    input 	  preamble_1;		// start of block
    input 	  preamble_2;		// start of subframe_A
    input 	  preamble_3;		// start of subframe_B
    input 	  carrier_loss;		// too many biphase violations
    input 	  biphase_violation;	// no transition at end of bit

    output 	  clock_out;		// clock selected from xtal
    output [3:0]  rx_status;		// status outputs
    output 	  parity;		// parity of current subframe
    output 	  load_A;		// load subframe_A from shift_reg
    output 	  load_B;		// load subframe_B from shift_reg
    output 	  load_buff;		// load register bank into buffer
    output [19:0] shift_reg;		// last 20 bits from phase_decoder
    output [1:0]  frame_ofs;		// last 2 bits of frame counter

    reg [6:0] 	  bit_count_A;	
    reg [6:0] 	  bit_count_B;
    reg [8:0] 	  frame_counter;

    reg 	  clock_out;
    reg  	  rx_status_3, rx_status_2, rx_status_1, rx_status_0;
    reg 	  parity;
    reg 	  load_A;
    reg 	  load_B;
    reg 	  load_buff;
    reg [19:0] 	  shift_reg;
    reg [3:0]    pc;
    
    parameter L0 = 0;
    parameter L1 = 1;
    parameter L2 = 2;
    parameter L3 = 3;
    parameter L4 = 4;
    parameter L5 = 5;
    parameter L6 = 6;
    parameter L7 = 7;
    parameter L8 = 8;
    parameter L9 = 9;
    parameter L10 = 10;


    assign 	  rx_status = {rx_status_3, rx_status_2,
			       rx_status_1, rx_status_0};

  initial begin
	bit_count_A = 0;
	bit_count_B = 0;
	frame_counter = 0;
	clock_out = 0;  // was uninitialized
	rx_status_3 = 0; rx_status_2 = 0; rx_status_1 = 0; rx_status_0 = 0;
	parity = 0;
	load_A = 0;
	load_B = 0;
	load_buff = 0;
	shift_reg = 0;
	pc = L0;
  end

  assign frame_ofs[1:0] = frame_counter[1:0];

  always @ (posedge clock) begin
	if (reset) begin
	    rx_status_3 = 0; rx_status_2 = 0;
	    load_A = 0;
	    load_B = 0;
	    load_buff = 0;
	    bit_count_A = 0;
	    bit_count_B = 0;
	    frame_counter = 0;
	    pc = L0;
	end else begin // if (reset)
	    case (pc)
	      L0: if (rx_control[2]) pc = L1; 	// wait for enable
	      L1: begin
		  case (rx_control[1:0])
		    2'b00: clock_out = xtal[0];
		    2'b01: clock_out = xtal[1];
		    2'b10: clock_out = xtal[2];
		    2'b11: clock_out = xtal[3];
		  endcase
		  pc = L2;
	      end
	      L2: // checking for start of block - preamble_1
		if (preamble_1) begin
		    // preamble_1 comes after 4 bits
		    bit_count_A = 4;
		    pc = L3;
		end
	      L3: if (bit_count_A < 32) begin
		  // load_A at end of subframe
		  if (bit_count_A == 31) load_A = 1;
		  // end of pulse on load_B
		  if (bit_count_A == 2) load_B = 0;
		  // if we have 4 full frames we have to activate load_buff
		  if (bit_count_A == 3) load_buff = 1;
		  if (bit_count_A == 5) load_buff = 0;
		  bit_count_A = bit_count_A + 1;
	      end else pc = L4;
	      L4: begin
	    	  bit_count_B = 1;
		  // update the frame counter too in the same cycle
		  frame_counter = 1;
		  // continue with subframe B
		  pc = L5;
	      end
	      L5: if (bit_count_B < 32) begin
		  if ((bit_count_B == 4) && (preamble_3 == 0))
		    rx_status_2 = 1; 
		  // load_B at end of subframe
		  if (bit_count_B == 31) load_B = 1;
		  // end of pulse on load_A
		  if (bit_count_B == 2) load_A = 0;
		  bit_count_B = bit_count_B + 1;
	      end else pc = L6;
	      L6: if (frame_counter < 191) begin
		  bit_count_A = 1;
		  // subframe A
		  pc = L7;
	      end else pc = L0;
	      L7: if (bit_count_A < 32) begin
		  if ((bit_count_A == 4) && (preamble_2 == 0))
  		    rx_status_2 = 1;
		  // load_A at end of subframe
		  if (bit_count_A == 31) load_A = 1;
		  // end of pulse on load_B
		  if (bit_count_A == 2) load_B = 0;
		  // if we have 4 full frames we have to activate load_buff
		  if (bit_count_A == 3) begin
   		      if (frame_counter[1:0] == 0) load_buff = 1;
		  end
		  if (bit_count_A == 5) load_buff = 0;
		  bit_count_A = bit_count_A + 1;
	      end else pc = L8;
	      L8: begin
		  bit_count_B = 1;
		  pc = L9;
	      end
	      L9: // subframe B
		if (bit_count_B < 32) begin
		    if ((bit_count_B == 4) && (preamble_3 == 0))
  		      rx_status_2 = 1; 
		    // load_B at end of subframe
		    if (bit_count_B == 31) load_B = 1;
		    // end of pulse on load_A
		    if (bit_count_B == 2) load_A = 0;
		    bit_count_B = bit_count_B + 1;
		end else pc = L10;
	      L10: begin
		  frame_counter = frame_counter + 1;
		  pc = L6;
	      end
	    endcase
	end
    end

    always @ (posedge clock) begin
	if (reset) begin
	    shift_reg = 0;
	    rx_status_1 = 0; rx_status_0 = 0;
	end else if (pc != L0 && pc != L1) begin
	    shift_reg = {shift_reg[18:0], bit_in};
	    if (carrier_loss) rx_status_0 = 1; 
	    if (biphase_violation) rx_status_1 = 1;
	end
    end // always @ (posedge clock)

  always @ (posedge clock) begin
	 if (reset || pc == L2 || pc == L4 || pc == L6 || pc == L8) begin
	   parity = 0;
	 end else if (pc != L0 && pc != L1) begin
	   parity = parity ^ bit_in;
	 end
  end

endmodule // daio_receiver
