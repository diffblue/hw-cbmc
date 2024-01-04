module main(input clk);

  function isUpper;
  input [7:0] in;
  begin
      isUpper = ~in[5];
  end
  endfunction

  // same function used in combinational and clocked logic  

  wire [7:0] my_wire1;
  reg my_wire2;

  always @my_wire1
    my_wire2 <= isUpper(my_wire1);

  reg my_reg;

  always @(posedge clk) begin
    my_reg = isUpper(my_wire1);
    assert (my_reg == my_wire2);
  end

endmodule
