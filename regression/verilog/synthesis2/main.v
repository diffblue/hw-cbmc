module main(input clk);
  reg [31:0] var0, var1, var2;

  initial var0=0;  
  initial var1=0;  
  initial var2=0;

  // var0 should be a wire
  always @var2
    var0=var2*2;

  // var1 should be a latch, as the old value is used
  always @var2
    if(var2[0]==0)
      var1=var2;

  // var2 sould be a flip-flop
  always @(posedge clk)
    var2=var2+1;

  // should pass
  always assert p0: var0[0]==0;
  always assert p1: var1[0]==0;

endmodule

module main_testbench;
  reg clk;
  integer i;

  main my_main(clk);

  initial begin
    for(i=0; i<10; i=i+1) begin
      $display("var1: %2d, var2: %2d", my_main.var1, my_main.var2);
      clk=0; #1; clk=1; #1;
    end
  end

endmodule
