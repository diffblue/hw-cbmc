module main;

  typedef int some_identifier;

  generate
    if(1) begin : some_block_label
      genvar some_identifier;
      for(some_identifier = 0; some_identifier < 10; some_identifier++);
    end
  endgenerate

endmodule
