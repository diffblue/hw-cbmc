module top(input clock, input i1);

  reg my_bit;
  reg [31:0] counter;

  initial my_bit=1;
  initial counter=0;

  always @(posedge clock) begin
    my_bit=my_bit;
    counter=counter+1;
  end
  
  p00: assert property (my_bit);
  p01: assert property (always my_bit);
  p02: assert property (counter==3 |-> nexttime counter==4);
  p03: assert property (counter==3 |=> counter==4);
  p04: assert property (counter==3 |=> nexttime counter==5);
  p05: assert property (s_eventually counter==8);
  p06: assert property (counter==0 |-> s_eventually counter==8);
  p07: assert property (counter==0 |-> counter<=5 until counter==6);
  p08: assert property (counter==0 |-> counter<=5 s_until counter==6);
  p09: assert property (counter==0 |-> counter<=5 until_with counter==5);
  p10: assert property (counter==0 |-> counter<=5 s_until_with counter==5);

endmodule

