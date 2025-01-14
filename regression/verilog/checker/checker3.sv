checker myChecker(property p);
  assert property (p);
endchecker

module main(input clk);
  reg [31:0] counter = 0;
  always_ff @(posedge clk) counter++;

  property my_prop;
    counter != 10
  endproperty;

  myChecker c(my_prop);
endmodule
