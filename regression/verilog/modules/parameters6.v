// A parameter may depend on a parameter that is declared later.
module my_module;

  parameter p = q;
  parameter q = 31;

endmodule
