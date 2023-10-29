// Null modem connection of the transmittin part of a UART to the
// receiving part of the same. This model is meant to test the
// correctness of the operation of the UART and of the handshaking
// between the controller and the UART.
//
// The controller reads data from a parallel port into a transmit buffer
// when load=1 and sends them to the UART when the latter is available for
// transmission. It also checks the UART to see if there are data
// available. If there are data, the controller reads them in a buffer.
//
// The reset signal (active low) resets the UART and reinitializes
// transmission process in the controller. It is still possible to load
// data in the transmit buffer while reset is active.
//
// Every latch in this model is controlled by the positive edge of clock.
// This clock is conceptually the receiver clock, which is 16 times
// faster than the transmission clock. All "slow" flip-flops use an
// enable signal.
//
// Partial correctness of operation is expressed by the following LTL
// formula:
//           GF (reset=0 + load=1) + FG ok=1
//
// which says that on all infinite computation paths along which reset or
// load are not active infinitely often, then ok is eventually always 1.
// The CTL equivalent is:
//
//           AG AF (reset=0 + load=1)  with fairness constraint ok=0
//
// Author: Fabio Somenzi <Fabio@Colorado.EDU>
// The UART is translated from the VHDL of Ben Cohen.

module nullModem(clock,reset,load,dataIn,ok);
    input       clock;		// active edge is positive one
    input       reset;		// active low
    input       load;		// load data into the transmit buffer
    input [7:0] dataIn;		// data to be loaded
    output 	ok;		// transfer is correct

    wire [7:0] 	parallelOut;	// data from the controller to the UART
    wire [7:0]  parallelIn;	// data from the UART to the controller
    wire 	shiftLoad;	// transmission control 
    wire 	enable;		// transmission control (clock gating)
    wire 	serialOut;	// serial data from the UART
    wire 	txEmpty;	// transmission status
    wire 	serialIn;	// serial data to the UART
    wire 	dataRdy;	// reception status
    wire 	bitClock;	// reception status (unused)

    reg 	rst;		// these two latches are for VIS, so that
    reg 	ld;		// CTL properties do not depend on PIs

  initial begin
	rst = 1;
	ld = 0;
    end
  
    always @ (posedge clock) begin
	rst = reset;
	ld = load;
    end

    control ctl(clock,rst,ld,dataIn,enable,parallelOut,parallelIn,shiftLoad,txEmpty,dataRdy,bitClock,ok);
    UartXmt Tx(shiftLoad,enable,clock,parallelOut,rst,serialOut,txEmpty);
    UartRx  Rx(clock,rst,serialIn,dataRdy,parallelIn,bitClock);
   
    assign serialIn = serialOut;		// null modem
   
    assert property (rst == 0 || ld == 1);
endmodule // nullModem


module control(clock,reset,ld,dataIn,enable,parallelOut,
	       parallelIn,shiftLoad,txEmpty,dataRdy,bitClock,ok);
    input        clock;
    input 	 reset;
    input 	 ld;
    input [7:0]  dataIn;
    output 	 enable;
    output [7:0] parallelOut;
    input [7:0]  parallelIn;
    output 	 shiftLoad;
    input 	 txEmpty;
    input 	 dataRdy;
    input 	 bitClock;
    output 	 ok;

    reg [7:0] 	 rxBuf;
    reg [7:0] 	 txBuf;
    reg 	 shiftLoad;
    reg [3:0] 	 freqDiv;

   initial begin
	rxBuf = 8'b10000000;  txBuf = 8'b00000001; // arbitrary
	shiftLoad = 1;
	freqDiv = 0;
    end
  
  always @ (posedge clock) begin
	if (reset == 0) begin
	    shiftLoad = 1;
	    freqDiv = 0;
	    if (ld == 1) begin
		txBuf = dataIn;
	    end
	end
	else begin
	    if (dataRdy == 1) begin
		rxBuf = parallelIn;
	    end // if (dataRdy == 1)

	    if (enable == 1 && txEmpty == 1) begin
		if (shiftLoad == 1) begin
		    shiftLoad = 0;
		end // if (shifLoad == 1)
		else begin
		    shiftLoad = 1;
		end // else: !if(shifLoad == 1)
	    end // if (txEmpty)
	    else if (ld == 1) begin
		txBuf = dataIn;
	    end

	    freqDiv = freqDiv + 1;

	end // else: !if(reset == 0)
    end // always @ (posedge clock)
    
    assign enable = freqDiv == 7;
    assign ok = rxBuf == txBuf;
    assign parallelOut = txBuf;

endmodule // control


//  Purpose:   Models the receive portion of a UART.
//
module UartRx(Clk16xT,ResetF,Serial_InT,DataRdyT,DataOuT,BitClkT);
    input        Clk16xT;
    input        ResetF;
    input        Serial_InT;
    output       DataRdyT;
    output [7:0] DataOuT;
    output 	 BitClkT;

    parameter 	 RxInit_c = 10'b1111111111;
    reg [9:0] 	 RxReg;		// the receive register
    reg [3:0] 	 Count16;	// to divide by 16
    reg 	 RxMT;		// receive register empty
    reg 	 RxIn;		// registered serial input

  initial begin
	RxReg = RxInit_c;
	Count16 = 0;
	RxMT = 1;
	RxIn = 0;
    end // initial begin

    always @ (posedge Clk16xT) begin
	// Reset
	if (ResetF == 0) begin
	    Count16 = 0;		// reset divide by 16 counter
	    RxMT = 1;			// new message starting
	    RxReg = RxInit_c;
	end

	// Start bit   
	else if (RxMT == 1 && RxIn == 0) begin
	    Count16 = 0;		// reset divide by 16 counter
	    RxMT = 0;			// new message starting
	    RxReg = RxInit_c;
	end

	// If in a receive transaction mode
	// if @ mid bit clock then clock data into register
	else if (Count16 == 7 && RxMT == 0) begin	// mid clock
	    RxReg[8:0] = RxReg[9:1];
	    RxReg[9] = RxIn;
	    Count16 = Count16 + 1;
	end

	// Normal counter increment modulo 16
	else begin
	    Count16 = Count16 + 1;
	end

	// Clock serial input into RxIn
	RxIn = Serial_InT;

	// Check if a data word is received
	if (DataRdyT == 1) begin 
	    RxMT = 1;
	end
    end // always @ (posedge Clk16xT)

    assign DataRdyT = RxMT == 0 && RxReg[9] == 1 && RxReg[0] == 0;

    assign BitClkT = Count16 == 9;

    assign DataOuT = RxReg[8:1];

endmodule // UartRx


//-----------------------------------------------------------------------------
//  Purpose:  Models the transmit register of a UART.
//            Operation is as follows:
//            . All operations occur on rising edge of CLK.
//            . If ResetF == 0 then
//                XmitReg is reset to 1111111111.
//                Count   is reset to 0.
//            . If ClkEnbT == 1 and Shift_LdF == 0 and ResetF == 1 then
//                {1'b1, DataT, 1'b0} gets loaded into XmitReg.
//                Count is reset to 0
//            . If ClkEnbT == 1 and Shift_LdF == 1 and ResetF == 1 then
//                {1'b1, XmitReg[9:1]} gets loaded into XmitReg
//                (shift right with a 1 shifted in)
//                Count is incremented to less than 10
//                (i.e. if it is 9, then it stays at 9)
//-----------------------------------------------------------------------------
module UartXmt(Shift_LdF,ClkEnbT,Clk,DataT,ResetF,Serial_OuT,XmitMT);
    input       Shift_LdF;
    input       ClkEnbT; 
    input       Clk;
    input [7:0] DataT;
    input 	ResetF;
    output 	Serial_OuT;	// serial output
    output 	XmitMT;		// transmitter empty

    reg [9:0] 	XmitReg;	// the transmit register
    reg [3:0] 	Count;		// # of serial bits sent
  

    initial begin
	Count = 0;
	XmitReg = 10'b1111111111;
    end // initial begin

    always @ (posedge Clk) begin
	if (ResetF == 0) begin
	    XmitReg = 10'b1111111111;
	    Count   = 9;
	end
	else if (ClkEnbT == 1 && Shift_LdF == 0 && ResetF == 1) begin
	    XmitReg[9]   = 1;		// stop bit(s)
	    XmitReg[8:1] = DataT;	// payload
	    XmitReg[0]   = 0;		// start bit
	    Count        = 0;
	end
	else if (ClkEnbT == 1 && Shift_LdF == 1 && ResetF == 1) begin
	    XmitReg[8:0] = XmitReg[9:1];
	    XmitReg[9]   = 1;
	    if (Count != 9)
	      Count = Count + 1;
	end
    end

    assign Serial_OuT = XmitReg[0];

    assign XmitMT = Count == 9;

endmodule // UartXmt
