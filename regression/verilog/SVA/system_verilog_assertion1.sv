module main();

  reg [31:0] x;
  wire clk;
  
  initial x=1;

  always @(posedge clk) begin
    x<=x+1;
    // an immediate assertion
    my_property: assert (x!=10)
      $display("Pass");
    else
      $display("Fail");
  end

endmodule
