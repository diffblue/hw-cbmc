About
=======

EBMC is a bounded model checker for the Verilog language (and other HW
specification languages).  The verification is performed by synthesizing a
transition system from the Verilog, unwinding the transition system (up to a
certain bound), and then producing a decision problem.  The decision problem
encodes the circuit and the negation of the property under verification. 
Hence if satisfiable, the tool produces a counterexample demonstrating
violation of the property.  EBMC can use CBMC's bit-vector solver or Z3
or CVC4 to solve the decision problem.

For full information see [cprover.org](http://www.cprover.org/ebmc/).

Usage
=====

Let us assume we have the following SystemVerilog code in `main.sv`.

```main.sv
module main(input clk, x, y);

  reg [1:0] cnt1;
  reg z;

  initial cnt1=0;
  initial z=0;

  always @(posedge clk) cnt1=cnt1+1;

  always @(posedge clk)
    casex (cnt1)
      2'b00:;
      2'b01:;
      2'b1?: z=1;
    endcase

  p1: assert property (@(posedge clk) (z==0));

endmodule
```

Then we can run the EBMC verification as

`$> ebmc main.sv --module main --bound 3`

setting the unwinding bound to `3` and running the verification of the module `main`.

For more information see [EBMC Manual](http://www.cprover.org/ebmc/manual/)
