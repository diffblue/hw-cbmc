About
=======

HW-CBMC (formerly EBMC) is a free, open-source formal verification tool for hardware designs.
It can read Verilog 2005, SystemVerilog 2017, NuSMV and netlists (given in
ISCAS89 format).  Properties can be given in LTL or a fragment of
SystemVerilog Assertions.  It includes both bounded and (despite its name)
unbounded Model Checking engines, i.e., it can both discover bugs and prove
the absence of bugs.

For full information see [cprover.org](http://www.cprover.org/ebmc/).

Usage
=====

Let us assume we have the following SystemVerilog model in `main.sv`.

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

We can then invoke the BMC engine in HW-CBMC as follows:

`$ hw-cbmc main.sv --top main --bound 3`

This sets the unwinding bound to `3` and the top-level module to `main`.

For more information see [HW-CBMC Manual](http://www.cprover.org/ebmc/manual/).
