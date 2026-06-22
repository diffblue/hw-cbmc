module aes_round(input clk, input [127:0] state_in, input [127:0] round_key,
                 output reg [127:0] state_out);
  function [7:0] sbox;
    input [7:0] b;
    sbox = b ^ {b[6:0], b[7]} ^ {b[5:0], b[7:6]} ^ 8'h63;
  endfunction
  function [7:0] xtime;
    input [7:0] b;
    xtime = {b[6:0], 1'b0} ^ (b[7] ? 8'h1b : 8'h00);
  endfunction

  wire [127:0] after_sub;
  assign after_sub = {sbox(state_in[127:120]), sbox(state_in[119:112]),
                      sbox(state_in[111:104]), sbox(state_in[103:96]),
                      sbox(state_in[95:88]),   sbox(state_in[87:80]),
                      sbox(state_in[79:72]),   sbox(state_in[71:64]),
                      sbox(state_in[63:56]),   sbox(state_in[55:48]),
                      sbox(state_in[47:40]),   sbox(state_in[39:32]),
                      sbox(state_in[31:24]),   sbox(state_in[23:16]),
                      sbox(state_in[15:8]),    sbox(state_in[7:0])};

  wire [7:0] b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15;
  assign {b0,b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15} = after_sub;

  // ShiftRows
  wire [7:0] s0=b0, s1=b5, s2=b10, s3=b15;
  wire [7:0] s4=b4, s5=b9, s6=b14, s7=b3;
  wire [7:0] s8=b8, s9=b13, s10=b2, s11=b7;
  wire [7:0] s12=b12, s13=b1, s14=b6, s15=b11;

  // MixColumns col 0
  wire [7:0] m0 = xtime(s0)^xtime(s1)^s1^s2^s3;
  wire [7:0] m1 = s0^xtime(s1)^xtime(s2)^s2^s3;
  wire [7:0] m2 = s0^s1^xtime(s2)^xtime(s3)^s3;
  wire [7:0] m3 = xtime(s0)^s0^s1^s2^xtime(s3);
  // MixColumns col 1
  wire [7:0] m4 = xtime(s4)^xtime(s5)^s5^s6^s7;
  wire [7:0] m5 = s4^xtime(s5)^xtime(s6)^s6^s7;
  wire [7:0] m6 = s4^s5^xtime(s6)^xtime(s7)^s7;
  wire [7:0] m7 = xtime(s4)^s4^s5^s6^xtime(s7);
  // MixColumns col 2
  wire [7:0] m8 = xtime(s8)^xtime(s9)^s9^s10^s11;
  wire [7:0] m9 = s8^xtime(s9)^xtime(s10)^s10^s11;
  wire [7:0] m10 = s8^s9^xtime(s10)^xtime(s11)^s11;
  wire [7:0] m11 = xtime(s8)^s8^s9^s10^xtime(s11);
  // MixColumns col 3
  wire [7:0] m12 = xtime(s12)^xtime(s13)^s13^s14^s15;
  wire [7:0] m13 = s12^xtime(s13)^xtime(s14)^s14^s15;
  wire [7:0] m14 = s12^s13^xtime(s14)^xtime(s15)^s15;
  wire [7:0] m15 = xtime(s12)^s12^s13^s14^xtime(s15);

  always @(posedge clk)
    state_out <= {m0,m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12,m13,m14,m15} ^ round_key;
endmodule
