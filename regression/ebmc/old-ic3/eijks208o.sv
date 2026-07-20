module eijks208o (i2,i4,i6,i8,i10,i12,i14,i16,i18,i20,p0);

input i2,i4,i6,i8,i10,i12,i14,i16,i18,i20;

output p0;

wire na66,a74,na80,na92,na98,a106,na114,na124,na138,a146,na152,na164,na170,a178,na186,
na196,a54,a56,a58,a60,a62,a64,a66,a68,a70,a72,a76,a78,a80,a82,
a84,a86,a88,a90,a92,a94,a96,a98,a100,a102,a104,a108,a110,a112,a114,
a116,a118,a120,a122,a124,a126,a128,a130,a132,a134,a136,a138,a140,a142,a144,
a148,a150,a152,a154,a156,a158,a160,a162,a164,a166,a168,a170,a172,a174,a176,
a180,a182,a184,a186,a188,a190,a192,a194,a196,a198,a200,a202,a204,a206,a208,
a210,a212,a214,a216,a218,a220,a222,a224,a226,a228,a230,a232,a234,a236,a238,
a240,a242,a244,a246,a248,a250,a252,a254,a256,a258,a260,a262,a264,a266,a268,
a270,a272,a274,a276,a278,a280,a282,a284,a286,a288,a290,a292,a294,a296,a298,
a300,a302,a304,a306,a308,a310,a312,a314,a316,a318,a320,a322,a324,a326,a328,
a330,a332,a334,a336,a338,a340,a342,a344,p0;

reg l22,l24,l26,l28,l30,l32,l34,l36,l38,l40,l42,l44,l46,l48,l50,
l52;

initial
begin
   l22 = 0;
   l24 = 0;
   l26 = 0;
   l28 = 0;
   l30 = 0;
   l32 = 0;
   l34 = 0;
   l36 = 0;
   l38 = 0;
   l40 = 0;
   l42 = 0;
   l44 = 0;
   l46 = 0;
   l48 = 0;
   l50 = 0;
   l52 = 0;
end

always @(posedge na66)
   l22 <= na66;

always @(posedge a74)
   l24 <= a74;

always @(posedge na80)
   l26 <= na80;

always @(posedge na92)
   l28 <= na92;

always @(posedge na98)
   l30 <= na98;

always @(posedge a106)
   l32 <= a106;

always @(posedge na114)
   l34 <= na114;

always @(posedge na124)
   l36 <= na124;

always @(posedge na138)
   l38 <= na138;

always @(posedge a146)
   l40 <= a146;

always @(posedge na152)
   l42 <= na152;

always @(posedge na164)
   l44 <= na164;

always @(posedge na170)
   l46 <= na170;

always @(posedge a178)
   l48 <= a178;

always @(posedge na186)
   l50 <= na186;

always @(posedge na196)
   l52 <= na196;


assign na66 = ~a66;
assign a74 = ~a72 & ~a70;
assign na80 = ~a80;
assign na92 = ~a92;
assign na98 = ~a98;
assign a106 = ~a104 & ~a102;
assign na114 = ~a114;
assign na124 = ~a124;
assign na138 = ~a138;
assign a146 = ~a144 & ~a142;
assign na152 = ~a152;
assign na164 = ~a164;
assign na170 = ~a170;
assign a178 = ~a176 & ~a174;
assign na186 = ~a186;
assign na196 = ~a196;
assign a54 = l32 & l30;
assign a56 = a54 & l34;
assign a58 = a56 & l36;
assign a60 = a58 & i2;
assign a62 = a60 & ~l22;
assign a64 = ~a60 & l22;
assign a66 = ~a64 & ~a62;
assign a68 = a60 & l22;
assign a70 = ~a68 & ~l24;
assign a72 = a68 & l24;
assign a76 = a72 & ~l26;
assign a78 = ~a72 & l26;
assign a80 = ~a78 & ~a76;
assign a82 = l26 & l24;
assign a84 = a82 & a68;
assign a86 = ~a84 & l28;
assign a88 = ~l28 & l26;
assign a90 = a88 & a72;
assign a92 = ~a90 & ~a86;
assign a94 = ~l30 & i2;
assign a96 = l30 & ~i2;
assign a98 = ~a96 & ~a94;
assign a100 = l30 & i2;
assign a102 = ~a100 & ~l32;
assign a104 = a100 & l32;
assign a108 = a54 & i2;
assign a110 = ~a108 & l34;
assign a112 = a108 & ~l34;
assign a114 = ~a112 & ~a110;
assign a116 = a56 & i2;
assign a118 = ~a116 & l36;
assign a120 = a108 & l34;
assign a122 = a120 & ~l36;
assign a124 = ~a122 & ~a118;
assign a126 = l48 & l46;
assign a128 = a126 & l50;
assign a130 = a128 & l52;
assign a132 = a130 & i2;
assign a134 = a132 & ~l38;
assign a136 = ~a132 & l38;
assign a138 = ~a136 & ~a134;
assign a140 = a132 & l38;
assign a142 = ~a140 & ~l40;
assign a144 = a140 & l40;
assign a148 = a144 & ~l42;
assign a150 = ~a144 & l42;
assign a152 = ~a150 & ~a148;
assign a154 = l42 & l40;
assign a156 = a154 & a140;
assign a158 = ~a156 & l44;
assign a160 = ~l44 & l42;
assign a162 = a160 & a144;
assign a164 = ~a162 & ~a158;
assign a166 = ~l46 & i2;
assign a168 = l46 & ~i2;
assign a170 = ~a168 & ~a166;
assign a172 = l46 & i2;
assign a174 = ~a172 & ~l48;
assign a176 = a172 & l48;
assign a180 = a126 & i2;
assign a182 = ~a180 & l50;
assign a184 = a180 & ~l50;
assign a186 = ~a184 & ~a182;
assign a188 = a128 & i2;
assign a190 = ~a188 & l52;
assign a192 = a180 & l50;
assign a194 = a192 & ~l52;
assign a196 = ~a194 & ~a190;
assign a198 = a94 & ~l32;
assign a200 = a198 & ~l34;
assign a202 = a200 & l36;
assign a204 = a202 & i12;
assign a206 = ~l32 & ~l30;
assign a208 = a206 & ~l36;
assign a210 = a208 & ~l34;
assign a212 = l22 & i2;
assign a214 = a212 & a210;
assign a216 = a214 & i10;
assign a218 = ~a216 & ~a204;
assign a220 = ~l22 & i2;
assign a222 = a220 & l24;
assign a224 = a222 & a210;
assign a226 = a224 & i8;
assign a228 = a220 & ~l24;
assign a230 = a228 & l26;
assign a232 = a230 & a210;
assign a234 = a232 & i6;
assign a236 = ~a234 & ~a226;
assign a238 = a236 & a218;
assign a240 = i20 & i2;
assign a242 = a100 & i18;
assign a244 = ~a242 & ~a240;
assign a246 = a94 & l32;
assign a248 = a246 & i16;
assign a250 = a198 & l34;
assign a252 = a250 & i14;
assign a254 = ~a252 & ~a248;
assign a256 = a254 & a244;
assign a258 = a256 & a238;
assign a260 = a228 & ~l26;
assign a262 = a260 & l28;
assign a264 = a262 & a210;
assign a266 = a264 & i4;
assign a268 = ~a266 & a258;
assign a270 = a166 & ~l48;
assign a272 = a270 & ~l50;
assign a274 = a272 & l52;
assign a276 = a274 & i12;
assign a278 = ~l48 & ~l46;
assign a280 = a278 & ~l52;
assign a282 = a280 & ~l50;
assign a284 = l38 & i2;
assign a286 = a284 & a282;
assign a288 = a286 & i10;
assign a290 = ~a288 & ~a276;
assign a292 = ~l38 & i2;
assign a294 = a292 & l40;
assign a296 = a294 & a282;
assign a298 = a296 & i8;
assign a300 = a292 & ~l40;
assign a302 = a300 & l42;
assign a304 = a302 & a282;
assign a306 = a304 & i6;
assign a308 = ~a306 & ~a298;
assign a310 = a308 & a290;
assign a312 = a172 & i18;
assign a314 = ~a312 & ~a240;
assign a316 = a166 & l48;
assign a318 = a316 & i16;
assign a320 = a270 & l50;
assign a322 = a320 & i14;
assign a324 = ~a322 & ~a318;
assign a326 = a324 & a314;
assign a328 = a326 & a310;
assign a330 = a300 & ~l42;
assign a332 = a330 & l44;
assign a334 = a332 & a282;
assign a336 = a334 & i4;
assign a338 = ~a336 & a328;
assign a340 = ~a338 & a268;
assign a342 = a338 & ~a268;
assign a344 = ~a342 & ~a340;
assign p0 = ~a344;

assert property (~p0);

endmodule
