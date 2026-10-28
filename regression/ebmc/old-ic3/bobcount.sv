module bobcount (i2,i4,i6,p0);

input i2,i4,i6;

output p0;

wire c1,a88,a96,a104,a114,na116,na124,na130,na136,na142,na148,na182,na186,a34,a36,
a38,a40,a42,a44,a46,a48,a50,a52,a54,a56,a58,a60,a62,a64,a66,
a68,a70,a72,a74,a76,a78,a80,a82,a84,a86,a90,a92,a94,a98,a100,
a102,a106,a108,a110,a112,a116,a118,a120,a122,a124,a126,a128,a130,a132,a134,
a136,a138,a140,a142,a144,a146,a148,a150,a152,a154,a156,a158,a160,a162,a164,
a166,a168,a170,a172,a174,a176,a178,a180,a182,a184,a186,p0;

reg l8,l10,l12,l14,l16,l18,l20,l22,l24,l26,l28,l30,l32;

initial
begin
   l8 = 0;
   l10 = 0;
   l12 = 0;
   l14 = 0;
   l16 = 0;
   l18 = 0;
   l20 = 0;
   l22 = 0;
   l24 = 0;
   l26 = 0;
   l28 = 0;
   l30 = 0;
   l32 = 0;
end

always @(posedge c1)
   l8 <= c1;

always @(posedge a88)
   l10 <= a88;

always @(posedge a96)
   l12 <= a96;

always @(posedge a104)
   l14 <= a104;

always @(posedge a114)
   l16 <= a114;

always @(posedge na116)
   l18 <= na116;

always @(posedge na124)
   l20 <= na124;

always @(posedge na130)
   l22 <= na130;

always @(posedge na136)
   l24 <= na136;

always @(posedge na142)
   l26 <= na142;

always @(posedge na148)
   l28 <= na148;

always @(posedge na182)
   l30 <= na182;

always @(posedge na186)
   l32 <= na186;


assign c1 = 1;
assign a88 = ~a86 & l8;
assign a96 = ~a94 & l8;
assign a104 = ~a102 & l8;
assign a114 = ~a112 & l8;
assign na116 = ~a116;
assign na124 = ~a124;
assign na130 = ~a130;
assign na136 = ~a136;
assign na142 = ~a142;
assign na148 = ~a148;
assign na182 = ~a182;
assign na186 = ~a186;
assign a34 = l20 & ~l8;
assign a36 = ~l20 & l8;
assign a38 = ~a36 & ~a34;
assign a40 = l22 & ~l10;
assign a42 = ~l22 & l10;
assign a44 = ~a42 & ~a40;
assign a46 = a44 & a38;
assign a48 = l24 & ~l12;
assign a50 = ~l24 & l12;
assign a52 = ~a50 & ~a48;
assign a54 = a52 & a46;
assign a56 = l26 & ~l14;
assign a58 = ~l26 & l14;
assign a60 = ~a58 & ~a56;
assign a62 = a60 & a54;
assign a64 = l28 & ~l16;
assign a66 = ~l28 & l16;
assign a68 = ~a66 & ~a64;
assign a70 = a68 & a62;
assign a72 = a70 & l18;
assign a74 = l32 & ~l30;
assign a76 = a74 & a72;
assign a78 = l14 & i4;
assign a80 = a78 & l12;
assign a82 = a80 & ~l10;
assign a84 = ~a80 & l10;
assign a86 = ~a84 & ~a82;
assign a90 = a78 & ~l12;
assign a92 = ~a78 & l12;
assign a94 = ~a92 & ~a90;
assign a98 = ~l14 & i4;
assign a100 = l14 & ~i4;
assign a102 = ~a100 & ~a98;
assign a106 = a80 & l10;
assign a108 = a106 & ~l16;
assign a110 = ~a106 & l16;
assign a112 = ~a110 & ~a108;
assign a116 = ~l18 & ~i6;
assign a118 = ~l18 & i6;
assign a120 = ~a118 & l20;
assign a122 = a118 & l8;
assign a124 = ~a122 & ~a120;
assign a126 = ~a118 & l22;
assign a128 = a118 & l10;
assign a130 = ~a128 & ~a126;
assign a132 = ~a118 & l24;
assign a134 = a118 & l12;
assign a136 = ~a134 & ~a132;
assign a138 = ~a118 & l26;
assign a140 = a118 & l14;
assign a142 = ~a140 & ~a138;
assign a144 = ~a118 & l28;
assign a146 = a118 & l16;
assign a148 = ~a146 & ~a144;
assign a150 = ~l14 & l12;
assign a152 = l14 & ~l12;
assign a154 = ~a152 & ~a150;
assign a156 = l14 & l12;
assign a158 = ~a156 & a154;
assign a160 = l16 & l10;
assign a162 = ~l16 & ~l10;
assign a164 = ~a162 & ~a160;
assign a166 = l16 & ~l10;
assign a168 = ~a166 & a164;
assign a170 = ~a168 & a158;
assign a172 = a168 & ~a158;
assign a174 = ~a172 & ~a170;
assign a176 = ~a168 & ~a158;
assign a178 = ~a176 & a174;
assign a180 = a178 & ~a116;
assign a182 = ~a180 & ~l30;
assign a184 = ~a116 & i4;
assign a186 = ~a184 & ~l32;
assign p0 = a76;

assert property (~p0);

endmodule
