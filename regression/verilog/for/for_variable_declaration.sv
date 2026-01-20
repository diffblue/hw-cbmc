module main;

  logic [1:0] some_logic;

  always_comb begin
    for (int i=0; i<2; i++) begin
      some_logic[i] <= 1'b0;
    end
  end

endmodule
