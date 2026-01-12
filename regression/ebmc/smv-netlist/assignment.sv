module main(some_input);

  input wire [1:0]  some_input;
  logic  [1:0]      data;

  assign data[0] = some_input[0];
  assign data[1] = some_input[1] & ~data[0];

  // should fail
  assert property(!data[1]);
   
endmodule 

