module my_add(input a, input b, output [1:0] y);

  assign y[0]=a^b;
  assign y[1]=a&b;

endmodule

module main(input a, input b);

  wire [1:0] result;

  my_add adder(a, b, result);

  assert property (a+b==result);

endmodule
