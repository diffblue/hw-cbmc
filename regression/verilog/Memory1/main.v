
`define ic_size 63
`define ic_msb  9

// RAM  MODULE
module main (adr,di,clk);
  input [`ic_msb:3] adr ;
  input [31:0] di ;
  input clk ;
  reg [`ic_msb:3] old_adr;
  reg [31:0] old_di;
  reg [7:0] ic_ram [`ic_size:0] ;

  initial ic_ram[0]=128;

  always @(posedge clk)
    ic_ram[{adr,3'b011}] = di[7:0];

  always assert property1: ic_ram[0] == 128;

endmodule
