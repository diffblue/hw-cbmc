module main;

  var [31:0] data;

  always_comb begin
    data[31:00] = 32'h0000_0010;
    data[15:08] = 24'hffff_20;
    data[23:16] = 16'h0030;
    data[31:24] = 08'h40;
  end

  assert final (data == 32'h40302010);

endmodule
