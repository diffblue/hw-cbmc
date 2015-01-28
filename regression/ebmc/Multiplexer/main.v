module main(select, d, q);
 input [1:0] select;
 input [3:0] d;
 output q;
 reg q;
 integer t;
 wire [1:0] select;
 wire [3:0] d;
 always @(select or d)
 begin
   case(select)
    0: q = d[0];
    1: q = d[1];
    2: q = d[2];
    3: q = d[3];
   endcase

assert property1: !(select==0) || (q == d[0]);
assert property2: !(select==1) || (q == d[1]);
assert property3: !(select==2) || (q == d[2]);
assert property4: !(select==3) || (q == d[3]);
 end
endmodule
