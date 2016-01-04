module main(clk);
  input clk;
  reg [31:0] x;

  task my_task1;
    input [31:0] in;
    output [31:0] out;
    out=in+1;
  endtask

  initial x=0;
  
  always @(posedge clk) begin
    my_task1(x, x);
  end

  // fails after 3 ticks  
  always assert property1: x<3;
  
endmodule
