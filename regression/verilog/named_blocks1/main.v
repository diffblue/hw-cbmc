module m;

  wire clock;

  always @(posedge clock) begin : my_block
  
    reg [31:0] x;
    if(x==10)
      x=1;
    else
      x=x+1;

    begin // unnamed
      begin : other_block // named
        reg [31:0] y;
        y=20;
      end
    end

    $display("my_block.x: %d", x);
    $display("my_block.other.block.y: %d", other_block.y);
  end
  
  initial my_block.x=1;
  
  always assert p1: my_block.x>=1 && my_block.x<=10;

  // Another x! Not to be confused with my_block.x.
  reg [7:0] x;
  
  initial x=2;

endmodule
