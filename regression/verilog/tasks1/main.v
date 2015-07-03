module main;

  task some_task;
    input [31:0] some_input;
    output [31:0] some_output;
    some_output = some_input+1;
  endtask

  reg [31:0] x, y;
  
  always @x begin
    some_task(x, y);
  end

  assert p1: y==x+1;

endmodule
