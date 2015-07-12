module main(clk);
  input clk;
  reg [31:0] x;

  task my_task1;
    x=x+1;
  endtask

  task my_task2;
    input [31:0] bound;
    if(x>=bound) x=0;
  endtask

  initial x=0;
  
  always @(posedge clk) begin
    my_task1;    
    my_task2(5);
  end
  
  always assert property1: x<5;

endmodule
