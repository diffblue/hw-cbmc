module main;

  real non_array;

  initial begin
    // $size expects an array or integral argument.
    // Returns 0 when using
    // Riviera Pro, Questa 2025.2, VCS 2025.06, Icarus Verilog.
    // Errored by Xcelium 25.03.
    int i = $size(non_array);
    $display(i);
  end

endmodule
