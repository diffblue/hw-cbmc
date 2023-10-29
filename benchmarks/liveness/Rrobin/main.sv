// Verilog model for the round-robin arbiter described in
// the CHARME99 paper by Katz, Grumberg, and Geist.

// Author: Fabio Somenzi <Fabio@Colorado.EDU>

// Modified to check a liveness property.

module main(clock,ir0,ir1,ack0,ack1);
    input  clock;
    input  ir0, ir1;
    output ack0, ack1;

    reg    req0, req1, ack0, ack1, robin;

    initial begin
	ack0 = 0; ack1 = 0; robin = 0;
	req0 = ir0; req1 = ir1;	// nondeterministic initial requests
    end

    always @ (posedge clock) begin
	if (~req0)
	  ack0 = 0;		// no request -> no ack
	else if (~req1)
	  ack0 = 1;		// a single request
	else if (~ack0 & ~ack1)
	  ack0 = ~robin;	// simultaneous request assertions
	else
	  ack0 = ~ack0;		// both requesting: toggle ack
    end

    always @ (posedge clock) begin
	if (~req1)
	  ack1 = 0;		// no request -> no ack
	else if (~req0)
	  ack1 = 1;		// a single request
	else if (~ack0 & ~ack1)
	  ack1 = robin;		// simultaneous request assertions
	else
	  ack1 = ~ack1;		// both requesting: toggle ack
    end

    always @ (posedge clock) begin
	if (req0 & req1 & ~ack0 & ~ack1)
	  robin = ~robin;	// simultaneous request assertions
    end

    // Latched inputs.
    always @ (posedge clock) begin
	req0 = ir0;
	req1 = ir1;
    end

    p0: assert property (eventually (req0 |-> nexttime ack0));
    p1: assert property (eventually (req1 |-> nexttime ack1));
  
endmodule // rrobin
