module my_module(some_port);

  // other_port is not in the port list.
  // Icarus Verilog tolerates this.
  input some_port, other_port;

endmodule
