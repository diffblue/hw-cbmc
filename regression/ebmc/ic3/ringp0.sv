module ringp0 (i2,i4,i6,i8,i10,i12,i14,i16,i18,i20,i22,i24,i26,i28,i30,
p0);

input i2,i4,i6,i8,i10,i12,i14,i16,i18,i20,i22,i24,i26,i28,i30;

output p0;

wire a90,a100,a110,a118,a124,a130,a140,a148,a158,a166,a168,a368,c1,a82,a84,
a86,a88,a92,a94,a96,a98,a102,a104,a106,a108,a112,a114,a116,a120,a122,
a126,a128,a132,a134,a136,a138,a142,a144,a146,a150,a152,a154,a156,a160,a162,
a164,a170,a172,a174,a176,a178,a180,a182,a184,a186,a188,a190,a192,a194,a196,
a198,a200,a202,a204,a206,a208,a210,a212,a214,a216,a218,a220,a222,a224,a226,
a228,a230,a232,a234,a236,a238,a240,a242,a244,a246,a248,a250,a252,a254,a256,
a258,a260,a262,a264,a266,a268,a270,a272,a274,a276,a278,a280,a282,a284,a286,
a288,a290,a292,a294,a296,a298,a300,a302,a304,a306,a308,a310,a312,a314,a316,
a318,a320,a322,a324,a326,a328,a330,a332,a334,a336,a338,a340,a342,a344,a346,
a348,a350,a352,a354,a356,a358,a360,a362,a364,a366,a370,p0;

reg l32,l34,l36,l38,l40,l42,l44,l46,l48,l50,l52,l54,l56,l58,l60,
l62,l64,l66,l68,l70,l72,l74,l76,l78,l80;

initial
begin
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
   l54 = 0;
   l56 = 0;
   l58 = 0;
   l60 = 0;
   l62 = 0;
   l64 = 0;
   l66 = 0;
   l68 = 0;
   l70 = 0;
   l72 = 0;
   l74 = 0;
   l76 = 0;
   l78 = 0;
   l80 = 0;
end

always @(posedge a90)
   l32 <= a90;

always @(posedge a100)
   l34 <= a100;

always @(posedge a110)
   l36 <= a110;

always @(posedge i6)
   l38 <= i6;

always @(posedge i8)
   l40 <= i8;

always @(posedge i10)
   l42 <= i10;

always @(posedge i12)
   l44 <= i12;

always @(posedge i14)
   l46 <= i14;

always @(posedge i16)
   l48 <= i16;

always @(posedge i18)
   l50 <= i18;

always @(posedge i20)
   l52 <= i20;

always @(posedge i22)
   l54 <= i22;

always @(posedge i24)
   l56 <= i24;

always @(posedge i26)
   l58 <= i26;

always @(posedge a118)
   l60 <= a118;

always @(posedge a124)
   l62 <= a124;

always @(posedge a130)
   l64 <= a130;

always @(posedge a140)
   l66 <= a140;

always @(posedge a148)
   l68 <= a148;

always @(posedge a158)
   l70 <= a158;

always @(posedge a166)
   l72 <= a166;

always @(posedge i28)
   l74 <= i28;

always @(posedge a168)
   l76 <= a168;

always @(posedge a368)
   l78 <= a368;

always @(posedge c1)
   l80 <= c1;


assign a90 = a88 & l80;
assign a100 = a98 & l80;
assign a110 = a108 & l80;
assign a118 = ~a116 & l80;
assign a124 = ~a122 & l80;
assign a130 = ~a128 & l80;
assign a140 = ~a138 & l80;
assign a148 = ~a146 & l80;
assign a158 = ~a156 & l80;
assign a166 = ~a164 & l80;
assign a168 = ~a112 & l80;
assign a368 = ~a366 & ~a174;
assign c1 = 1;
assign a82 = ~i4 & ~i2;
assign a84 = a82 & l36;
assign a86 = ~a82 & ~l32;
assign a88 = ~a86 & ~a84;
assign a92 = i4 & ~i2;
assign a94 = a92 & l32;
assign a96 = ~a92 & ~l34;
assign a98 = ~a96 & ~a94;
assign a102 = ~i4 & i2;
assign a104 = a102 & l34;
assign a106 = ~a102 & ~l36;
assign a108 = ~a106 & ~a104;
assign a112 = ~l76 & ~l74;
assign a114 = ~a112 & a82;
assign a116 = ~a114 & ~l60;
assign a120 = ~a112 & a92;
assign a122 = ~a120 & ~l62;
assign a126 = ~a112 & a102;
assign a128 = ~a126 & ~l64;
assign a132 = ~l38 & l32;
assign a134 = ~a132 & l40;
assign a136 = ~a134 & ~a112;
assign a138 = ~a136 & ~l66;
assign a142 = l38 & l32;
assign a144 = ~a142 & ~a112;
assign a146 = ~a144 & ~l68;
assign a150 = ~l42 & ~l32;
assign a152 = ~a150 & l44;
assign a154 = ~a152 & ~a112;
assign a156 = ~a154 & ~l70;
assign a160 = l42 & ~l32;
assign a162 = ~a160 & ~a112;
assign a164 = ~a162 & ~l72;
assign a170 = ~i12 & i10;
assign a172 = a170 & ~i8;
assign a174 = a172 & ~l80;
assign a176 = a132 & ~l40;
assign a178 = ~l38 & ~l32;
assign a180 = a150 & ~l44;
assign a182 = ~l42 & l32;
assign a184 = ~a182 & ~a180;
assign a186 = a184 & ~a178;
assign a188 = a186 & ~a176;
assign a190 = ~l76 & l74;
assign a192 = a190 & ~l32;
assign a194 = ~a190 & ~l46;
assign a196 = ~a194 & ~a192;
assign a198 = a196 & ~i14;
assign a200 = ~a196 & i14;
assign a202 = ~a200 & ~a198;
assign a204 = a202 & a188;
assign a206 = a190 & ~l34;
assign a208 = ~a190 & ~l48;
assign a210 = ~a208 & ~a206;
assign a212 = a210 & ~i16;
assign a214 = ~a210 & i16;
assign a216 = ~a214 & ~a212;
assign a218 = a216 & a204;
assign a220 = a190 & ~l36;
assign a222 = ~a190 & ~l50;
assign a224 = ~a222 & ~a220;
assign a226 = a224 & ~i18;
assign a228 = ~a224 & i18;
assign a230 = ~a228 & ~a226;
assign a232 = a230 & a218;
assign a234 = a190 & ~l38;
assign a236 = ~a190 & ~l52;
assign a238 = ~a236 & ~a234;
assign a240 = a238 & ~i20;
assign a242 = ~a238 & i20;
assign a244 = ~a242 & ~a240;
assign a246 = a244 & a232;
assign a248 = a190 & ~l40;
assign a250 = ~a190 & ~l54;
assign a252 = ~a250 & ~a248;
assign a254 = a252 & ~i22;
assign a256 = ~a252 & i22;
assign a258 = ~a256 & ~a254;
assign a260 = a258 & a246;
assign a262 = a190 & ~l42;
assign a264 = ~a190 & ~l56;
assign a266 = ~a264 & ~a262;
assign a268 = a266 & ~i24;
assign a270 = ~a266 & i24;
assign a272 = ~a270 & ~a268;
assign a274 = a272 & a260;
assign a276 = a190 & ~l44;
assign a278 = ~a190 & ~l58;
assign a280 = ~a278 & ~a276;
assign a282 = a280 & ~i26;
assign a284 = ~a280 & i26;
assign a286 = ~a284 & ~a282;
assign a288 = a286 & a274;
assign a290 = ~l46 & l32;
assign a292 = l46 & ~l32;
assign a294 = ~a292 & ~a290;
assign a296 = ~l48 & l34;
assign a298 = l48 & ~l34;
assign a300 = ~a298 & ~a296;
assign a302 = ~l50 & l36;
assign a304 = l50 & ~l36;
assign a306 = ~a304 & ~a302;
assign a308 = l52 & ~l38;
assign a310 = ~l52 & l38;
assign a312 = ~a310 & ~a308;
assign a314 = l54 & ~l40;
assign a316 = ~l54 & l40;
assign a318 = ~a316 & ~a314;
assign a320 = l56 & ~l42;
assign a322 = ~l56 & l42;
assign a324 = ~a322 & ~a320;
assign a326 = l58 & ~l44;
assign a328 = ~l58 & l44;
assign a330 = ~a328 & ~a326;
assign a332 = a330 & a324;
assign a334 = a332 & a318;
assign a336 = a334 & a312;
assign a338 = a336 & a306;
assign a340 = a338 & a300;
assign a342 = a340 & a294;
assign a344 = a342 & l76;
assign a346 = a344 & l60;
assign a348 = a346 & l62;
assign a350 = a348 & l64;
assign a352 = a350 & l66;
assign a354 = a352 & l68;
assign a356 = a354 & l70;
assign a358 = a356 & l72;
assign a360 = ~a358 & i30;
assign a362 = ~a360 & l78;
assign a364 = a362 & a288;
assign a366 = ~a364 & l80;
assign a370 = a362 & i30;
assign p0 = a370;

assert property (~p0);

endmodule
