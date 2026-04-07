module main;

  initial begin : blk
    int i, j;
    j = 0;
    for(i = 0; i < 10; i++) begin
      if(i == 5)
        continue;
      j++;
    end
    p0: assert(j==9);
  end

endmodule
