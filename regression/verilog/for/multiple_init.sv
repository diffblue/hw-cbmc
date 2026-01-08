module main;

  initial begin
    int i, j;
    for(i = 0, j = 1; i < 10; i++) begin
    end
    assert(i==10);
    assert(j==1);
  end

endmodule
