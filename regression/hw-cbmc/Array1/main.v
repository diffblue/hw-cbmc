module top(input clk);

  reg [31:0] array[9:0];

  initial begin
    array[0]=0;
    array[1]=1;
    array[2]=2;
    array[3]=3;
    array[4]=4;
    array[5]=5;
    array[6]=6;
    array[7]=7;
    array[8]=8;
    array[9]=9;
  end

endmodule
