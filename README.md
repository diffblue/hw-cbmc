About
=======

EBMC is a bounded model checker for the Verilog language (and other HW
specification languages). The verification is performed by synthesizing a
transition system from the Verilog, unwinding the loops (up to a certain bound),
and then producing a SAT formula. The formula encodes the circuit and the
negation of the property under verification. Hence if satisfiable, the tool
produces a counterexample demonstrating violation of the property. EBMC employs
CBMC for the last two steps of the above described verification chain, i.e. SAT
encoding and satisfiability checking.

For full information see [cprover.org](http://www.cprover.org/ebmc/)

Compiling
=========

- initialize and update the CBMC submodule: `$> git submodule init; git submodule update`
- build EBMC: `$> cd src; make` (this also build CBMC internally)
- optionally: `$> export PATH=/full/path/hw-cbmc/src/ebmc:${PATH}` to get EBMC on the path

Usage
=====

Let us assume we have the following Verilog code in `main.v`

```main.v

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

  always assert p1: z==0;

endmodule

```

Then we can run the EBMC verification as

`$> ebmc main.v --module main --bound 3`

setting the unrolling bound to `3` and running the verification of the module `main`.

For more information see [EBMC Manual](http://www.cprover.org/ebmc/manual/)
