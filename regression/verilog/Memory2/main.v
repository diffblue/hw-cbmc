module main(input clk);
  reg [7:0] my_ram [20:0] ;

  initial my_ram[0]=1;
  initial my_ram[1]=2;
  initial my_ram[2]=3;
  initial my_ram[3]=4;
  initial my_ram[4]=5;

  always @(posedge clk)
    my_ram[1] = 3;
    
  wire [7:0] mem_out0 = my_ram[0];

  always assert property1: mem_out0 == 1;

endmodule
