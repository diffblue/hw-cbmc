module main;

  initial begin : blk1
    int x;
    x = 0;
    if(1)
      assert(1);
    else
      x = 1;

    // This passes if the 'else' binds to the if.
    // This passes for Riviera Pro 2025.04, and fails
    // for the others.
    P: assert(x == 1);
  end

  initial begin : blk2
    int x;
    x = 0;
    if(1)
      assert(1) ; else x = 1;

    // This passes if the 'else' binds to the assert.
    // This is the case for Icarus Verilog 12.0,
    // Xcelium 25.03, Questa 2025.2, VCS 2025.06.
    P: assert(x == 0);
  end

endmodule
