module sub;
  int i;
endmodule

module main;

  sub sub_inst();

  // Icarus Verilog says 0, whereas
  // Riviera Pro, Xcelium, Questa, VCS reject this.
  int N = $bits(sub_inst);

endmodule
