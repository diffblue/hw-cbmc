module main(clk);
  input clk;
  reg [31:0] x;
  reg [31:0] inc;

  task my_task1;
    inout [31:0] myarg;
    myarg=myarg+inc;
  endtask

  initial x=0;
  
  always @(posedge clk) begin
    inc=1;
    my_task1(x);
  end
  
  always assert property1: x<3;
  
endmodule
