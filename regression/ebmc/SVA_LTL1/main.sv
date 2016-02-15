module top(input clock, input i1);

  reg my_bit;
  reg [31:0] counter;

  initial my_bit=1;
  initial counter=0;

  always @(posedge clock) begin
    my_bit=my_bit;
    counter=counter+1;
  end
  
  p0: assert property (my_bit);
  p1: assert property (always my_bit);
  p2: assert property (counter==3 |-> nexttime counter==4);
  p3: assert property (counter==3 |=> counter==4);
  p4: assert property (counter==3 |=> nexttime counter==5);
  p5: assert property (eventually counter==8);

endmodule

