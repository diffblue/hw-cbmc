// Example of "bureaucrat" request/acknowledgement protocol.
// When a request is received, a timer is started and no action is taken
// until the timer signals that some time has elapsed.
// Because of the timer, this system is intrinsically hard to model check.
// The solution is the abstraction of the counter.
//
// Author: Fabio Somenzi <Fabio@Colorado.EDU>

// This environment module generates nondeterministic requests.
module main(clock);
    input clock;
    reg	  req;
    wire  ack;
    wire  nd;

    initial begin
	req = 0;
    end

    assign nd = 1; //$ND(0,1);

 always @ (posedge clock)
	req = nd;
    
  reqAck ra(clock,req,ack);
  
  assert property (req==1 |-> ##[1:10] ack==1);
endmodule // main

// This module 
module reqAck(clock,req,ack);
    input	    clock;
    input	    req;
    output	    ack;

    parameter 
	idle = 2'd0,
	starting = 2'd1,
	working = 2'd2,
	done = 2'd3;
    
    reg [1:0]	    state;
    wire	    start;
    wire	    ready;

    initial begin
	state = idle;
    end

    always @ (posedge clock) begin
	case (state)
	  idle:
	      begin
		  if (req)
		      state = starting;
		  else
		      state = idle;
	      end // case: idle
	  starting:
	      begin
		  state = working;
	      end // case: starting
	  working:
	      begin
		  if (ready)
		      state = done;
		  else
		      state = working;
	      end // case: working
	  done:
	      begin
		  state = idle;
	      end // case: done
	endcase // case (state)
    end // always @ (req or ready)

    assign ack = state == done;
    assign start = state == starting;


    slave slv(clock,start,ready);

endmodule // reqAck


// This module is a timer.
module slave(clock,start,ready);
    input     clock;
    input     start;
    output    ready;

    reg [9:0] count;

    initial begin
	count = 0;
    end

    always @ (posedge clock) begin
	if (start)
	    count = 0;
	else
	    count = count + 1;
    end // always @ (posedge clock)

    assign ready = count == 10'b0000000111; //10'b1111111111;

endmodule // slave
