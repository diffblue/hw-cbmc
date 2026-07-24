// End labels after endfunction/endtask, IEEE 1800-2017 A.9.3.
// Reduced from LogikBench blocks/hmac, blocks/i2c, blocks/uart, large/aes.
module main;

  function automatic bit is_width_valid(int width);
    unique case (width)
      16: return 1'b1;
      32: return 1'b1;
      default: return 1'b0;
    endcase
  endfunction : is_width_valid

  task set_zero(output int o);
    o = 0;
  endtask : set_zero

  initial begin
    assert(is_width_valid(16));
  end

endmodule
