// Model to check the equivalence of two different FIFO implementations.
// This example is taken from Ken McMillan's "A Conjunctively Decomposed
// Boolean Representation for Symbolic Model Checking" (CAV'96), though
// the details are probably different.
//
// Author: Fabio Somenzi <Fabio@Colorado.EDU>
//
// Modified to check a liveness property instead of equivalence.

module main(clock,dataIn);
    parameter	   MSBD = 3;
    parameter	   LAST = 15;
    parameter	   MSBA = 3;
    input	   clock;
    input [MSBD:0] dataIn;

    wire [MSBD:0]  srDataOut;
    wire	   srFull, srEmpty;
    wire [MSBD:0]  rbDataOut;
    wire	   rbFull, rbEmpty;

    srFIFO #(MSBD,LAST,MSBA) sr (clock, dataIn, 0, 1,
				srDataOut, srFull, srEmpty);

    p0: assert property (eventually srEmpty == 1);

endmodule // main


// Shift register FIFO.
// tail points to the first element of the queue unless the buffer is empty.
// the new data is always inserted in position 0 of the buffer, after
// shifting the contents up by one position.
// A push on a full buffer is a NOOP.
// A pop from an empty buffer is a NOOP.
// If both push and pop are asserted at the same clock cycle, only the push
// operation is performed.
// dataOut gives the first element of the queue unless the buffer is empty,
// in which case its value is arbitrary.
module srFIFO(clock,dataIn,push,pop,dataOut,full,empty);
    parameter	    MSBD = 3;
    parameter	    LAST = 15;
    parameter	    MSBA = 3;
    input	    clock;
    input [MSBD:0]  dataIn;
    input	    push;
    input	    pop;
    output [MSBD:0] dataOut;
    output	    full;
    output	    empty;

    reg [MSBD:0]    mem[0:LAST];
    reg [MSBA:0]    tail;
    reg		    empty;
    integer	    i;

    initial begin
	for (i = 0; i <= LAST; i = i + 1)
	    mem[i] = 0;
	tail = 0;
	empty = 1;
    end // initial begin

    always @ (posedge clock) begin
	if (push & ~full) begin
	    for (i = LAST; i > 0; i = i - 1)
		mem[i] = mem[i - 1];
	    mem[0] = dataIn;
	    if (~empty)
		tail = tail + 1;
	    empty = 0;
	end // if (push & ~full)
	else if (pop & ~empty) begin
	    if (tail == 0)
		empty = 1;
	    else
		tail = tail - 1;
	end // if (pop & ~empty)
    end // always @ (posedge clock)

    assign dataOut = mem[tail];
	
    assign full = tail == LAST;

endmodule // srFIFO
