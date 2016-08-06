module main(input clk, input something);
  reg [31:0] var;
  
  initial var[10:1]=0;

  // var[0] should be wire
  always @something
    var[0]=something;

  // var[10:1] sould be a flip-flop
  always @(posedge clk)
    var[10:1]=var[10:1]+1;

endmodule

module main_testbench;
  reg clk;
  integer i;
  reg something;

  main my_main(clk, something);

  initial begin
    for(i=0; i<10; i=i+1) begin
      something=i%2; #0;
      $display("something: %d, var[0]: %d, var[10:1]: %2d", 
               something, my_main.var[0], my_main.var[10:1]);
      clk=0; #1; clk=1; #1;
    end
  end

endmodule
