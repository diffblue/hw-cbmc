module main;

  var bit[31:0] some_var;
  var [$bits(some_var)-1:0] other_var;
  parameter param = $bits(other_var);

  p0: assert property (param == 32);

endmodule
