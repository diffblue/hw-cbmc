module main(input clk);

  reg [31:0] counter = 0;

  always @(posedge clk)
    counter++;

  initial p0: assert property ($stable(counter));
  initial p1: assert property (!$rose(counter));
  initial p2: assert property (!$fell(counter));
  initial p3: assert property (!$changed(counter));

  initial p4: assert property (##1 !$stable(counter));
  initial p5: assert property (##1 $rose(counter));
  initial p6: assert property (##1 !$fell(counter));
  initial p7: assert property (##1 $changed(counter));

endmodule
