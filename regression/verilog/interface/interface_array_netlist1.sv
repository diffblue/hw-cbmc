// An array of interface instances, with the netlist-based engines, which
// failed with "unimplemented boolbv_widtht::get_entry(verilog_module_instance)".
interface sif;
  logic v;
endinterface

module main(input clk, input a, input b);
  sif i[1:0]();
  assign i[0].v = a;
  assign i[1].v = b;
  wire o = i[0].v | i[1].v;
  reg q = 0;
  always @(posedge clk) q <= o;
  p0: assert property (@(posedge clk) (a | b) == o);
  p1: assert property (@(posedge clk) q == 0);   // fails
endmodule
