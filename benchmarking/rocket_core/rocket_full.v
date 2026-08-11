// See LICENSE.SiFive for license details.

//VCS coverage exclude_file

// No default parameter values are intended, nor does IEEE 1800-2012 require them (clause A.2.4 param_assignment),
// but Incisive demands them. These default values should never be used.
module plusarg_reader #(
   parameter FORMAT="borked=%d",
   parameter WIDTH=1,
   parameter [WIDTH-1:0] DEFAULT=0
) (
   output [WIDTH-1:0] out
);

`ifdef SYNTHESIS
assign out = DEFAULT;
`else
reg [WIDTH-1:0] myplus;
assign out = myplus;

initial begin
   if (!$value$plusargs(FORMAT, myplus)) myplus = DEFAULT;
end
`endif

endmodule
module RVCExpander(
  input  [31:0] io_in,
  output [31:0] io_out_bits,
  output [4:0]  io_out_rd,
  output [4:0]  io_out_rs1,
  output [4:0]  io_out_rs2,
  output        io_rvc
);
  wire [6:0] io_out_s_opc = |io_in[12:5] ? 7'h13 : 7'h1f; // @[RVC.scala 53:20]
  wire [4:0] _io_out_s_T_6 = {2'h1,io_in[4:2]}; // @[Cat.scala 31:58]
  wire [29:0] _io_out_s_T_7 = {io_in[10:7],io_in[12:11],io_in[5],io_in[6],2'h0,5'h2,3'h0,2'h1,io_in[4:2],io_out_s_opc}; // @[Cat.scala 31:58]
  wire [7:0] _io_out_s_T_15 = {io_in[6:5],io_in[12:10],3'h0}; // @[Cat.scala 31:58]
  wire [4:0] _io_out_s_T_17 = {2'h1,io_in[9:7]}; // @[Cat.scala 31:58]
  wire [27:0] _io_out_s_T_20 = {io_in[6:5],io_in[12:10],3'h0,2'h1,io_in[9:7],3'h3,2'h1,io_in[4:2],7'h7}; // @[Cat.scala 31:58]
  wire [6:0] _io_out_s_T_31 = {io_in[5],io_in[12:10],io_in[6],2'h0}; // @[Cat.scala 31:58]
  wire [26:0] _io_out_s_T_36 = {io_in[5],io_in[12:10],io_in[6],2'h0,2'h1,io_in[9:7],3'h2,2'h1,io_in[4:2],7'h3}; // @[Cat.scala 31:58]
  wire [26:0] _io_out_s_T_52 = {io_in[5],io_in[12:10],io_in[6],2'h0,2'h1,io_in[9:7],3'h2,2'h1,io_in[4:2],7'h7}; // @[Cat.scala 31:58]
  wire [26:0] _io_out_s_T_74 = {_io_out_s_T_31[6:5],2'h1,io_in[4:2],2'h1,io_in[9:7],3'h2,_io_out_s_T_31[4:0],7'h3f}; // @[Cat.scala 31:58]
  wire [27:0] _io_out_s_T_94 = {_io_out_s_T_15[7:5],2'h1,io_in[4:2],2'h1,io_in[9:7],3'h3,_io_out_s_T_15[4:0],7'h27}; // @[Cat.scala 31:58]
  wire [26:0] _io_out_s_T_116 = {_io_out_s_T_31[6:5],2'h1,io_in[4:2],2'h1,io_in[9:7],3'h2,_io_out_s_T_31[4:0],7'h23}; // @[Cat.scala 31:58]
  wire [26:0] _io_out_s_T_138 = {_io_out_s_T_31[6:5],2'h1,io_in[4:2],2'h1,io_in[9:7],3'h2,_io_out_s_T_31[4:0],7'h27}; // @[Cat.scala 31:58]
  wire [6:0] _io_out_s_T_148 = io_in[12] ? 7'h7f : 7'h0; // @[Bitwise.scala 74:12]
  wire [11:0] _io_out_s_T_150 = {_io_out_s_T_148,io_in[6:2]}; // @[Cat.scala 31:58]
  wire [31:0] io_out_s_8_bits = {_io_out_s_T_148,io_in[6:2],io_in[11:7],3'h0,io_in[11:7],7'h13}; // @[Cat.scala 31:58]
  wire [9:0] _io_out_s_T_161 = io_in[12] ? 10'h3ff : 10'h0; // @[Bitwise.scala 74:12]
  wire [20:0] _io_out_s_T_169 = {_io_out_s_T_161,io_in[8],io_in[10:9],io_in[6],io_in[7],io_in[2],io_in[11],io_in[5:3],1'h0
    }; // @[Cat.scala 31:58]
  wire [31:0] io_out_s_9_bits = {_io_out_s_T_169[20],_io_out_s_T_169[10:1],_io_out_s_T_169[11],_io_out_s_T_169[19:12],5'h1
    ,7'h6f}; // @[Cat.scala 31:58]
  wire [31:0] io_out_s_10_bits = {_io_out_s_T_148,io_in[6:2],5'h0,3'h0,io_in[11:7],7'h13}; // @[Cat.scala 31:58]
  wire  _io_out_s_opc_T_7 = |_io_out_s_T_150; // @[RVC.scala 90:29]
  wire [6:0] io_out_s_opc_1 = |_io_out_s_T_150 ? 7'h37 : 7'h3f; // @[RVC.scala 90:20]
  wire [14:0] _io_out_s_me_T_2 = io_in[12] ? 15'h7fff : 15'h0; // @[Bitwise.scala 74:12]
  wire [31:0] _io_out_s_me_T_4 = {_io_out_s_me_T_2,io_in[6:2],12'h0}; // @[Cat.scala 31:58]
  wire [31:0] io_out_s_me_bits = {_io_out_s_me_T_4[31:12],io_in[11:7],io_out_s_opc_1}; // @[Cat.scala 31:58]
  wire [6:0] io_out_s_opc_2 = _io_out_s_opc_T_7 ? 7'h13 : 7'h1f; // @[RVC.scala 86:20]
  wire [2:0] _io_out_s_T_230 = io_in[12] ? 3'h7 : 3'h0; // @[Bitwise.scala 74:12]
  wire [31:0] io_out_s_res_bits = {_io_out_s_T_230,io_in[4:3],io_in[5],io_in[2],io_in[6],4'h0,io_in[11:7],3'h0,io_in[11:
    7],io_out_s_opc_2}; // @[Cat.scala 31:58]
  wire [31:0] io_out_s_11_bits = io_in[11:7] == 5'h0 | io_in[11:7] == 5'h2 ? io_out_s_res_bits : io_out_s_me_bits; // @[RVC.scala 92:10]
  wire [4:0] io_out_s_11_rd = io_in[11:7] == 5'h0 | io_in[11:7] == 5'h2 ? io_in[11:7] : io_in[11:7]; // @[RVC.scala 92:10]
  wire [4:0] io_out_s_11_rs2 = io_in[11:7] == 5'h0 | io_in[11:7] == 5'h2 ? _io_out_s_T_6 : _io_out_s_T_6; // @[RVC.scala 92:10]
  wire [25:0] _io_out_s_T_251 = {io_in[12],io_in[6:2],2'h1,io_in[9:7],3'h5,2'h1,io_in[9:7],7'h13}; // @[Cat.scala 31:58]
  wire [30:0] _GEN_0 = {{5'd0}, _io_out_s_T_251}; // @[RVC.scala 99:23]
  wire [30:0] _io_out_s_T_260 = _GEN_0 | 31'h40000000; // @[RVC.scala 99:23]
  wire [31:0] _io_out_s_T_270 = {_io_out_s_T_148,io_in[6:2],2'h1,io_in[9:7],3'h7,2'h1,io_in[9:7],7'h13}; // @[Cat.scala 31:58]
  wire [2:0] _io_out_s_funct_T_2 = {io_in[12],io_in[6:5]}; // @[Cat.scala 31:58]
  wire [2:0] _io_out_s_funct_T_4 = _io_out_s_funct_T_2 == 3'h1 ? 3'h4 : 3'h0; // @[package.scala 32:76]
  wire [2:0] _io_out_s_funct_T_6 = _io_out_s_funct_T_2 == 3'h2 ? 3'h6 : _io_out_s_funct_T_4; // @[package.scala 32:76]
  wire [2:0] _io_out_s_funct_T_8 = _io_out_s_funct_T_2 == 3'h3 ? 3'h7 : _io_out_s_funct_T_6; // @[package.scala 32:76]
  wire [2:0] _io_out_s_funct_T_10 = _io_out_s_funct_T_2 == 3'h4 ? 3'h0 : _io_out_s_funct_T_8; // @[package.scala 32:76]
  wire [2:0] _io_out_s_funct_T_12 = _io_out_s_funct_T_2 == 3'h5 ? 3'h0 : _io_out_s_funct_T_10; // @[package.scala 32:76]
  wire [2:0] _io_out_s_funct_T_14 = _io_out_s_funct_T_2 == 3'h6 ? 3'h2 : _io_out_s_funct_T_12; // @[package.scala 32:76]
  wire [2:0] io_out_s_funct = _io_out_s_funct_T_2 == 3'h7 ? 3'h3 : _io_out_s_funct_T_14; // @[package.scala 32:76]
  wire [30:0] io_out_s_sub = io_in[6:5] == 2'h0 ? 31'h40000000 : 31'h0; // @[RVC.scala 103:22]
  wire [6:0] io_out_s_opc_3 = io_in[12] ? 7'h3b : 7'h33; // @[RVC.scala 104:22]
  wire [24:0] _io_out_s_T_277 = {2'h1,io_in[4:2],2'h1,io_in[9:7],io_out_s_funct,2'h1,io_in[9:7],io_out_s_opc_3}; // @[Cat.scala 31:58]
  wire [30:0] _GEN_1 = {{6'd0}, _io_out_s_T_277}; // @[RVC.scala 105:43]
  wire [30:0] _io_out_s_T_278 = _GEN_1 | io_out_s_sub; // @[RVC.scala 105:43]
  wire [30:0] _io_out_s_T_281 = io_in[11:10] == 2'h1 ? _io_out_s_T_260 : {{5'd0}, _io_out_s_T_251}; // @[package.scala 32:76]
  wire [31:0] _io_out_s_T_283 = io_in[11:10] == 2'h2 ? _io_out_s_T_270 : {{1'd0}, _io_out_s_T_281}; // @[package.scala 32:76]
  wire [31:0] io_out_s_12_bits = io_in[11:10] == 2'h3 ? {{1'd0}, _io_out_s_T_278} : _io_out_s_T_283; // @[package.scala 32:76]
  wire [31:0] io_out_s_13_bits = {_io_out_s_T_169[20],_io_out_s_T_169[10:1],_io_out_s_T_169[11],_io_out_s_T_169[19:12],5'h0
    ,7'h6f}; // @[Cat.scala 31:58]
  wire [4:0] _io_out_s_T_349 = io_in[12] ? 5'h1f : 5'h0; // @[Bitwise.scala 74:12]
  wire [12:0] _io_out_s_T_354 = {_io_out_s_T_349,io_in[6:5],io_in[2],io_in[11:10],io_in[4:3],1'h0}; // @[Cat.scala 31:58]
  wire [31:0] io_out_s_14_bits = {_io_out_s_T_354[12],_io_out_s_T_354[10:5],5'h0,2'h1,io_in[9:7],3'h0,_io_out_s_T_354[4:
    1],_io_out_s_T_354[11],7'h63}; // @[Cat.scala 31:58]
  wire [31:0] io_out_s_15_bits = {_io_out_s_T_354[12],_io_out_s_T_354[10:5],5'h0,2'h1,io_in[9:7],3'h1,_io_out_s_T_354[4:
    1],_io_out_s_T_354[11],7'h63}; // @[Cat.scala 31:58]
  wire  _io_out_s_load_opc_T_1 = |io_in[11:7]; // @[RVC.scala 113:27]
  wire [6:0] io_out_s_load_opc = |io_in[11:7] ? 7'h3 : 7'h1f; // @[RVC.scala 113:23]
  wire [25:0] _io_out_s_T_438 = {io_in[12],io_in[6:2],io_in[11:7],3'h1,io_in[11:7],7'h13}; // @[Cat.scala 31:58]
  wire [28:0] _io_out_s_T_448 = {io_in[4:2],io_in[12],io_in[6:5],3'h0,5'h2,3'h3,io_in[11:7],7'h7}; // @[Cat.scala 31:58]
  wire [27:0] _io_out_s_T_457 = {io_in[3:2],io_in[12],io_in[6:4],2'h0,5'h2,3'h2,io_in[11:7],io_out_s_load_opc}; // @[Cat.scala 31:58]
  wire [27:0] _io_out_s_T_466 = {io_in[3:2],io_in[12],io_in[6:4],2'h0,5'h2,3'h2,io_in[11:7],7'h7}; // @[Cat.scala 31:58]
  wire [24:0] _io_out_s_mv_T_2 = {io_in[6:2],5'h0,3'h0,io_in[11:7],7'h33}; // @[Cat.scala 31:58]
  wire [24:0] _io_out_s_add_T_3 = {io_in[6:2],io_in[11:7],3'h0,io_in[11:7],7'h33}; // @[Cat.scala 31:58]
  wire [24:0] io_out_s_jr = {io_in[6:2],io_in[11:7],3'h0,12'h67}; // @[Cat.scala 31:58]
  wire [24:0] io_out_s_reserved = {io_out_s_jr[24:7],7'h1f}; // @[Cat.scala 31:58]
  wire [24:0] _io_out_s_jr_reserved_T_2 = _io_out_s_load_opc_T_1 ? io_out_s_jr : io_out_s_reserved; // @[RVC.scala 134:33]
  wire  _io_out_s_jr_mv_T_1 = |io_in[6:2]; // @[RVC.scala 135:27]
  wire [31:0] io_out_s_mv_bits = {{7'd0}, _io_out_s_mv_T_2}; // @[RVC.scala 21:19 22:14]
  wire [31:0] io_out_s_jr_reserved_bits = {{7'd0}, _io_out_s_jr_reserved_T_2}; // @[RVC.scala 21:19 22:14]
  wire [31:0] io_out_s_jr_mv_bits = |io_in[6:2] ? io_out_s_mv_bits : io_out_s_jr_reserved_bits; // @[RVC.scala 135:22]
  wire [4:0] io_out_s_jr_mv_rd = |io_in[6:2] ? io_in[11:7] : 5'h0; // @[RVC.scala 135:22]
  wire [4:0] io_out_s_jr_mv_rs1 = |io_in[6:2] ? 5'h0 : io_in[11:7]; // @[RVC.scala 135:22]
  wire [4:0] io_out_s_jr_mv_rs2 = |io_in[6:2] ? io_in[6:2] : io_in[6:2]; // @[RVC.scala 135:22]
  wire [24:0] io_out_s_jalr = {io_in[6:2],io_in[11:7],3'h0,12'he7}; // @[Cat.scala 31:58]
  wire [24:0] _io_out_s_ebreak_T_1 = {io_out_s_jr[24:7],7'h73}; // @[Cat.scala 31:58]
  wire [24:0] io_out_s_ebreak = _io_out_s_ebreak_T_1 | 25'h100000; // @[RVC.scala 137:46]
  wire [24:0] _io_out_s_jalr_ebreak_T_2 = _io_out_s_load_opc_T_1 ? io_out_s_jalr : io_out_s_ebreak; // @[RVC.scala 138:33]
  wire [31:0] io_out_s_add_bits = {{7'd0}, _io_out_s_add_T_3}; // @[RVC.scala 21:19 22:14]
  wire [31:0] io_out_s_jalr_ebreak_bits = {{7'd0}, _io_out_s_jalr_ebreak_T_2}; // @[RVC.scala 21:19 22:14]
  wire [31:0] io_out_s_jalr_add_bits = _io_out_s_jr_mv_T_1 ? io_out_s_add_bits : io_out_s_jalr_ebreak_bits; // @[RVC.scala 139:25]
  wire [4:0] io_out_s_jalr_add_rd = _io_out_s_jr_mv_T_1 ? io_in[11:7] : 5'h1; // @[RVC.scala 139:25]
  wire [4:0] io_out_s_jalr_add_rs1 = _io_out_s_jr_mv_T_1 ? io_in[11:7] : io_in[11:7]; // @[RVC.scala 139:25]
  wire [31:0] io_out_s_20_bits = io_in[12] ? io_out_s_jalr_add_bits : io_out_s_jr_mv_bits; // @[RVC.scala 140:10]
  wire [4:0] io_out_s_20_rd = io_in[12] ? io_out_s_jalr_add_rd : io_out_s_jr_mv_rd; // @[RVC.scala 140:10]
  wire [4:0] io_out_s_20_rs1 = io_in[12] ? io_out_s_jalr_add_rs1 : io_out_s_jr_mv_rs1; // @[RVC.scala 140:10]
  wire [4:0] io_out_s_20_rs2 = io_in[12] ? io_out_s_jr_mv_rs2 : io_out_s_jr_mv_rs2; // @[RVC.scala 140:10]
  wire [8:0] _io_out_s_T_473 = {io_in[9:7],io_in[12:10],3'h0}; // @[Cat.scala 31:58]
  wire [28:0] _io_out_s_T_480 = {_io_out_s_T_473[8:5],io_in[6:2],5'h2,3'h3,_io_out_s_T_473[4:0],7'h27}; // @[Cat.scala 31:58]
  wire [7:0] _io_out_s_T_486 = {io_in[8:7],io_in[12:9],2'h0}; // @[Cat.scala 31:58]
  wire [27:0] _io_out_s_T_493 = {_io_out_s_T_486[7:5],io_in[6:2],5'h2,3'h2,_io_out_s_T_486[4:0],7'h23}; // @[Cat.scala 31:58]
  wire [27:0] _io_out_s_T_506 = {_io_out_s_T_486[7:5],io_in[6:2],5'h2,3'h2,_io_out_s_T_486[4:0],7'h27}; // @[Cat.scala 31:58]
  wire [4:0] io_out_s_24_rs1 = io_in[19:15]; // @[RVC.scala 20:57]
  wire [4:0] io_out_s_24_rs2 = io_in[24:20]; // @[RVC.scala 20:79]
  wire [4:0] _io_out_T_2 = {io_in[1:0],io_in[15:13]}; // @[Cat.scala 31:58]
  wire [31:0] io_out_s_1_bits = {{4'd0}, _io_out_s_T_20}; // @[RVC.scala 21:19 22:14]
  wire [31:0] io_out_s_0_bits = {{2'd0}, _io_out_s_T_7}; // @[RVC.scala 21:19 22:14]
  wire [31:0] _io_out_T_4_bits = _io_out_T_2 == 5'h1 ? io_out_s_1_bits : io_out_s_0_bits; // @[package.scala 32:76]
  wire [4:0] _io_out_T_4_rd = _io_out_T_2 == 5'h1 ? _io_out_s_T_6 : _io_out_s_T_6; // @[package.scala 32:76]
  wire [4:0] _io_out_T_4_rs1 = _io_out_T_2 == 5'h1 ? _io_out_s_T_17 : 5'h2; // @[package.scala 32:76]
  wire [31:0] io_out_s_2_bits = {{5'd0}, _io_out_s_T_36}; // @[RVC.scala 21:19 22:14]
  wire [31:0] _io_out_T_6_bits = _io_out_T_2 == 5'h2 ? io_out_s_2_bits : _io_out_T_4_bits; // @[package.scala 32:76]
  wire [4:0] _io_out_T_6_rd = _io_out_T_2 == 5'h2 ? _io_out_s_T_6 : _io_out_T_4_rd; // @[package.scala 32:76]
  wire [4:0] _io_out_T_6_rs1 = _io_out_T_2 == 5'h2 ? _io_out_s_T_17 : _io_out_T_4_rs1; // @[package.scala 32:76]
  wire [31:0] io_out_s_3_bits = {{5'd0}, _io_out_s_T_52}; // @[RVC.scala 21:19 22:14]
  wire [31:0] _io_out_T_8_bits = _io_out_T_2 == 5'h3 ? io_out_s_3_bits : _io_out_T_6_bits; // @[package.scala 32:76]
  wire [4:0] _io_out_T_8_rd = _io_out_T_2 == 5'h3 ? _io_out_s_T_6 : _io_out_T_6_rd; // @[package.scala 32:76]
  wire [4:0] _io_out_T_8_rs1 = _io_out_T_2 == 5'h3 ? _io_out_s_T_17 : _io_out_T_6_rs1; // @[package.scala 32:76]
  wire [31:0] io_out_s_4_bits = {{5'd0}, _io_out_s_T_74}; // @[RVC.scala 21:19 22:14]
  wire [31:0] _io_out_T_10_bits = _io_out_T_2 == 5'h4 ? io_out_s_4_bits : _io_out_T_8_bits; // @[package.scala 32:76]
  wire [4:0] _io_out_T_10_rd = _io_out_T_2 == 5'h4 ? _io_out_s_T_6 : _io_out_T_8_rd; // @[package.scala 32:76]
  wire [4:0] _io_out_T_10_rs1 = _io_out_T_2 == 5'h4 ? _io_out_s_T_17 : _io_out_T_8_rs1; // @[package.scala 32:76]
  wire [31:0] io_out_s_5_bits = {{4'd0}, _io_out_s_T_94}; // @[RVC.scala 21:19 22:14]
  wire [31:0] _io_out_T_12_bits = _io_out_T_2 == 5'h5 ? io_out_s_5_bits : _io_out_T_10_bits; // @[package.scala 32:76]
  wire [4:0] _io_out_T_12_rd = _io_out_T_2 == 5'h5 ? _io_out_s_T_6 : _io_out_T_10_rd; // @[package.scala 32:76]
  wire [4:0] _io_out_T_12_rs1 = _io_out_T_2 == 5'h5 ? _io_out_s_T_17 : _io_out_T_10_rs1; // @[package.scala 32:76]
  wire [31:0] io_out_s_6_bits = {{5'd0}, _io_out_s_T_116}; // @[RVC.scala 21:19 22:14]
  wire [31:0] _io_out_T_14_bits = _io_out_T_2 == 5'h6 ? io_out_s_6_bits : _io_out_T_12_bits; // @[package.scala 32:76]
  wire [4:0] _io_out_T_14_rd = _io_out_T_2 == 5'h6 ? _io_out_s_T_6 : _io_out_T_12_rd; // @[package.scala 32:76]
  wire [4:0] _io_out_T_14_rs1 = _io_out_T_2 == 5'h6 ? _io_out_s_T_17 : _io_out_T_12_rs1; // @[package.scala 32:76]
  wire [31:0] io_out_s_7_bits = {{5'd0}, _io_out_s_T_138}; // @[RVC.scala 21:19 22:14]
  wire [31:0] _io_out_T_16_bits = _io_out_T_2 == 5'h7 ? io_out_s_7_bits : _io_out_T_14_bits; // @[package.scala 32:76]
  wire [4:0] _io_out_T_16_rd = _io_out_T_2 == 5'h7 ? _io_out_s_T_6 : _io_out_T_14_rd; // @[package.scala 32:76]
  wire [4:0] _io_out_T_16_rs1 = _io_out_T_2 == 5'h7 ? _io_out_s_T_17 : _io_out_T_14_rs1; // @[package.scala 32:76]
  wire [31:0] _io_out_T_18_bits = _io_out_T_2 == 5'h8 ? io_out_s_8_bits : _io_out_T_16_bits; // @[package.scala 32:76]
  wire [4:0] _io_out_T_18_rd = _io_out_T_2 == 5'h8 ? io_in[11:7] : _io_out_T_16_rd; // @[package.scala 32:76]
  wire [4:0] _io_out_T_18_rs1 = _io_out_T_2 == 5'h8 ? io_in[11:7] : _io_out_T_16_rs1; // @[package.scala 32:76]
  wire [4:0] _io_out_T_18_rs2 = _io_out_T_2 == 5'h8 ? _io_out_s_T_6 : _io_out_T_16_rd; // @[package.scala 32:76]
  wire [31:0] _io_out_T_20_bits = _io_out_T_2 == 5'h9 ? io_out_s_9_bits : _io_out_T_18_bits; // @[package.scala 32:76]
  wire [4:0] _io_out_T_20_rd = _io_out_T_2 == 5'h9 ? 5'h1 : _io_out_T_18_rd; // @[package.scala 32:76]
  wire [4:0] _io_out_T_20_rs1 = _io_out_T_2 == 5'h9 ? io_in[11:7] : _io_out_T_18_rs1; // @[package.scala 32:76]
  wire [4:0] _io_out_T_20_rs2 = _io_out_T_2 == 5'h9 ? _io_out_s_T_6 : _io_out_T_18_rs2; // @[package.scala 32:76]
  wire [31:0] _io_out_T_22_bits = _io_out_T_2 == 5'ha ? io_out_s_10_bits : _io_out_T_20_bits; // @[package.scala 32:76]
  wire [4:0] _io_out_T_22_rd = _io_out_T_2 == 5'ha ? io_in[11:7] : _io_out_T_20_rd; // @[package.scala 32:76]
  wire [4:0] _io_out_T_22_rs1 = _io_out_T_2 == 5'ha ? 5'h0 : _io_out_T_20_rs1; // @[package.scala 32:76]
  wire [4:0] _io_out_T_22_rs2 = _io_out_T_2 == 5'ha ? _io_out_s_T_6 : _io_out_T_20_rs2; // @[package.scala 32:76]
  wire [31:0] _io_out_T_24_bits = _io_out_T_2 == 5'hb ? io_out_s_11_bits : _io_out_T_22_bits; // @[package.scala 32:76]
  wire [4:0] _io_out_T_24_rd = _io_out_T_2 == 5'hb ? io_out_s_11_rd : _io_out_T_22_rd; // @[package.scala 32:76]
  wire [4:0] _io_out_T_24_rs1 = _io_out_T_2 == 5'hb ? io_out_s_11_rd : _io_out_T_22_rs1; // @[package.scala 32:76]
  wire [4:0] _io_out_T_24_rs2 = _io_out_T_2 == 5'hb ? io_out_s_11_rs2 : _io_out_T_22_rs2; // @[package.scala 32:76]
  wire [31:0] _io_out_T_26_bits = _io_out_T_2 == 5'hc ? io_out_s_12_bits : _io_out_T_24_bits; // @[package.scala 32:76]
  wire [4:0] _io_out_T_26_rd = _io_out_T_2 == 5'hc ? _io_out_s_T_17 : _io_out_T_24_rd; // @[package.scala 32:76]
  wire [4:0] _io_out_T_26_rs1 = _io_out_T_2 == 5'hc ? _io_out_s_T_17 : _io_out_T_24_rs1; // @[package.scala 32:76]
  wire [4:0] _io_out_T_26_rs2 = _io_out_T_2 == 5'hc ? _io_out_s_T_6 : _io_out_T_24_rs2; // @[package.scala 32:76]
  wire [31:0] _io_out_T_28_bits = _io_out_T_2 == 5'hd ? io_out_s_13_bits : _io_out_T_26_bits; // @[package.scala 32:76]
  wire [4:0] _io_out_T_28_rd = _io_out_T_2 == 5'hd ? 5'h0 : _io_out_T_26_rd; // @[package.scala 32:76]
  wire [4:0] _io_out_T_28_rs1 = _io_out_T_2 == 5'hd ? _io_out_s_T_17 : _io_out_T_26_rs1; // @[package.scala 32:76]
  wire [4:0] _io_out_T_28_rs2 = _io_out_T_2 == 5'hd ? _io_out_s_T_6 : _io_out_T_26_rs2; // @[package.scala 32:76]
  wire [31:0] _io_out_T_30_bits = _io_out_T_2 == 5'he ? io_out_s_14_bits : _io_out_T_28_bits; // @[package.scala 32:76]
  wire [4:0] _io_out_T_30_rd = _io_out_T_2 == 5'he ? _io_out_s_T_17 : _io_out_T_28_rd; // @[package.scala 32:76]
  wire [4:0] _io_out_T_30_rs1 = _io_out_T_2 == 5'he ? _io_out_s_T_17 : _io_out_T_28_rs1; // @[package.scala 32:76]
  wire [4:0] _io_out_T_30_rs2 = _io_out_T_2 == 5'he ? 5'h0 : _io_out_T_28_rs2; // @[package.scala 32:76]
  wire [31:0] _io_out_T_32_bits = _io_out_T_2 == 5'hf ? io_out_s_15_bits : _io_out_T_30_bits; // @[package.scala 32:76]
  wire [4:0] _io_out_T_32_rd = _io_out_T_2 == 5'hf ? 5'h0 : _io_out_T_30_rd; // @[package.scala 32:76]
  wire [4:0] _io_out_T_32_rs1 = _io_out_T_2 == 5'hf ? _io_out_s_T_17 : _io_out_T_30_rs1; // @[package.scala 32:76]
  wire [4:0] _io_out_T_32_rs2 = _io_out_T_2 == 5'hf ? 5'h0 : _io_out_T_30_rs2; // @[package.scala 32:76]
  wire [31:0] io_out_s_16_bits = {{6'd0}, _io_out_s_T_438}; // @[RVC.scala 21:19 22:14]
  wire [31:0] _io_out_T_34_bits = _io_out_T_2 == 5'h10 ? io_out_s_16_bits : _io_out_T_32_bits; // @[package.scala 32:76]
  wire [4:0] _io_out_T_34_rd = _io_out_T_2 == 5'h10 ? io_in[11:7] : _io_out_T_32_rd; // @[package.scala 32:76]
  wire [4:0] _io_out_T_34_rs1 = _io_out_T_2 == 5'h10 ? io_in[11:7] : _io_out_T_32_rs1; // @[package.scala 32:76]
  wire [4:0] _io_out_T_34_rs2 = _io_out_T_2 == 5'h10 ? io_in[6:2] : _io_out_T_32_rs2; // @[package.scala 32:76]
  wire [31:0] io_out_s_17_bits = {{3'd0}, _io_out_s_T_448}; // @[RVC.scala 21:19 22:14]
  wire [31:0] _io_out_T_36_bits = _io_out_T_2 == 5'h11 ? io_out_s_17_bits : _io_out_T_34_bits; // @[package.scala 32:76]
  wire [4:0] _io_out_T_36_rd = _io_out_T_2 == 5'h11 ? io_in[11:7] : _io_out_T_34_rd; // @[package.scala 32:76]
  wire [4:0] _io_out_T_36_rs1 = _io_out_T_2 == 5'h11 ? 5'h2 : _io_out_T_34_rs1; // @[package.scala 32:76]
  wire [4:0] _io_out_T_36_rs2 = _io_out_T_2 == 5'h11 ? io_in[6:2] : _io_out_T_34_rs2; // @[package.scala 32:76]
  wire [31:0] io_out_s_18_bits = {{4'd0}, _io_out_s_T_457}; // @[RVC.scala 21:19 22:14]
  wire [31:0] _io_out_T_38_bits = _io_out_T_2 == 5'h12 ? io_out_s_18_bits : _io_out_T_36_bits; // @[package.scala 32:76]
  wire [4:0] _io_out_T_38_rd = _io_out_T_2 == 5'h12 ? io_in[11:7] : _io_out_T_36_rd; // @[package.scala 32:76]
  wire [4:0] _io_out_T_38_rs1 = _io_out_T_2 == 5'h12 ? 5'h2 : _io_out_T_36_rs1; // @[package.scala 32:76]
  wire [4:0] _io_out_T_38_rs2 = _io_out_T_2 == 5'h12 ? io_in[6:2] : _io_out_T_36_rs2; // @[package.scala 32:76]
  wire [31:0] io_out_s_19_bits = {{4'd0}, _io_out_s_T_466}; // @[RVC.scala 21:19 22:14]
  wire [31:0] _io_out_T_40_bits = _io_out_T_2 == 5'h13 ? io_out_s_19_bits : _io_out_T_38_bits; // @[package.scala 32:76]
  wire [4:0] _io_out_T_40_rd = _io_out_T_2 == 5'h13 ? io_in[11:7] : _io_out_T_38_rd; // @[package.scala 32:76]
  wire [4:0] _io_out_T_40_rs1 = _io_out_T_2 == 5'h13 ? 5'h2 : _io_out_T_38_rs1; // @[package.scala 32:76]
  wire [4:0] _io_out_T_40_rs2 = _io_out_T_2 == 5'h13 ? io_in[6:2] : _io_out_T_38_rs2; // @[package.scala 32:76]
  wire [31:0] _io_out_T_42_bits = _io_out_T_2 == 5'h14 ? io_out_s_20_bits : _io_out_T_40_bits; // @[package.scala 32:76]
  wire [4:0] _io_out_T_42_rd = _io_out_T_2 == 5'h14 ? io_out_s_20_rd : _io_out_T_40_rd; // @[package.scala 32:76]
  wire [4:0] _io_out_T_42_rs1 = _io_out_T_2 == 5'h14 ? io_out_s_20_rs1 : _io_out_T_40_rs1; // @[package.scala 32:76]
  wire [4:0] _io_out_T_42_rs2 = _io_out_T_2 == 5'h14 ? io_out_s_20_rs2 : _io_out_T_40_rs2; // @[package.scala 32:76]
  wire [31:0] io_out_s_21_bits = {{3'd0}, _io_out_s_T_480}; // @[RVC.scala 21:19 22:14]
  wire [31:0] _io_out_T_44_bits = _io_out_T_2 == 5'h15 ? io_out_s_21_bits : _io_out_T_42_bits; // @[package.scala 32:76]
  wire [4:0] _io_out_T_44_rd = _io_out_T_2 == 5'h15 ? io_in[11:7] : _io_out_T_42_rd; // @[package.scala 32:76]
  wire [4:0] _io_out_T_44_rs1 = _io_out_T_2 == 5'h15 ? 5'h2 : _io_out_T_42_rs1; // @[package.scala 32:76]
  wire [4:0] _io_out_T_44_rs2 = _io_out_T_2 == 5'h15 ? io_in[6:2] : _io_out_T_42_rs2; // @[package.scala 32:76]
  wire [31:0] io_out_s_22_bits = {{4'd0}, _io_out_s_T_493}; // @[RVC.scala 21:19 22:14]
  wire [31:0] _io_out_T_46_bits = _io_out_T_2 == 5'h16 ? io_out_s_22_bits : _io_out_T_44_bits; // @[package.scala 32:76]
  wire [4:0] _io_out_T_46_rd = _io_out_T_2 == 5'h16 ? io_in[11:7] : _io_out_T_44_rd; // @[package.scala 32:76]
  wire [4:0] _io_out_T_46_rs1 = _io_out_T_2 == 5'h16 ? 5'h2 : _io_out_T_44_rs1; // @[package.scala 32:76]
  wire [4:0] _io_out_T_46_rs2 = _io_out_T_2 == 5'h16 ? io_in[6:2] : _io_out_T_44_rs2; // @[package.scala 32:76]
  wire [31:0] io_out_s_23_bits = {{4'd0}, _io_out_s_T_506}; // @[RVC.scala 21:19 22:14]
  wire [31:0] _io_out_T_48_bits = _io_out_T_2 == 5'h17 ? io_out_s_23_bits : _io_out_T_46_bits; // @[package.scala 32:76]
  wire [4:0] _io_out_T_48_rd = _io_out_T_2 == 5'h17 ? io_in[11:7] : _io_out_T_46_rd; // @[package.scala 32:76]
  wire [4:0] _io_out_T_48_rs1 = _io_out_T_2 == 5'h17 ? 5'h2 : _io_out_T_46_rs1; // @[package.scala 32:76]
  wire [4:0] _io_out_T_48_rs2 = _io_out_T_2 == 5'h17 ? io_in[6:2] : _io_out_T_46_rs2; // @[package.scala 32:76]
  wire [31:0] _io_out_T_50_bits = _io_out_T_2 == 5'h18 ? io_in : _io_out_T_48_bits; // @[package.scala 32:76]
  wire [4:0] _io_out_T_50_rd = _io_out_T_2 == 5'h18 ? io_in[11:7] : _io_out_T_48_rd; // @[package.scala 32:76]
  wire [4:0] _io_out_T_50_rs1 = _io_out_T_2 == 5'h18 ? io_out_s_24_rs1 : _io_out_T_48_rs1; // @[package.scala 32:76]
  wire [4:0] _io_out_T_50_rs2 = _io_out_T_2 == 5'h18 ? io_out_s_24_rs2 : _io_out_T_48_rs2; // @[package.scala 32:76]
  wire [31:0] _io_out_T_52_bits = _io_out_T_2 == 5'h19 ? io_in : _io_out_T_50_bits; // @[package.scala 32:76]
  wire [4:0] _io_out_T_52_rd = _io_out_T_2 == 5'h19 ? io_in[11:7] : _io_out_T_50_rd; // @[package.scala 32:76]
  wire [4:0] _io_out_T_52_rs1 = _io_out_T_2 == 5'h19 ? io_out_s_24_rs1 : _io_out_T_50_rs1; // @[package.scala 32:76]
  wire [4:0] _io_out_T_52_rs2 = _io_out_T_2 == 5'h19 ? io_out_s_24_rs2 : _io_out_T_50_rs2; // @[package.scala 32:76]
  wire [31:0] _io_out_T_54_bits = _io_out_T_2 == 5'h1a ? io_in : _io_out_T_52_bits; // @[package.scala 32:76]
  wire [4:0] _io_out_T_54_rd = _io_out_T_2 == 5'h1a ? io_in[11:7] : _io_out_T_52_rd; // @[package.scala 32:76]
  wire [4:0] _io_out_T_54_rs1 = _io_out_T_2 == 5'h1a ? io_out_s_24_rs1 : _io_out_T_52_rs1; // @[package.scala 32:76]
  wire [4:0] _io_out_T_54_rs2 = _io_out_T_2 == 5'h1a ? io_out_s_24_rs2 : _io_out_T_52_rs2; // @[package.scala 32:76]
  wire [31:0] _io_out_T_56_bits = _io_out_T_2 == 5'h1b ? io_in : _io_out_T_54_bits; // @[package.scala 32:76]
  wire [4:0] _io_out_T_56_rd = _io_out_T_2 == 5'h1b ? io_in[11:7] : _io_out_T_54_rd; // @[package.scala 32:76]
  wire [4:0] _io_out_T_56_rs1 = _io_out_T_2 == 5'h1b ? io_out_s_24_rs1 : _io_out_T_54_rs1; // @[package.scala 32:76]
  wire [4:0] _io_out_T_56_rs2 = _io_out_T_2 == 5'h1b ? io_out_s_24_rs2 : _io_out_T_54_rs2; // @[package.scala 32:76]
  wire [31:0] _io_out_T_58_bits = _io_out_T_2 == 5'h1c ? io_in : _io_out_T_56_bits; // @[package.scala 32:76]
  wire [4:0] _io_out_T_58_rd = _io_out_T_2 == 5'h1c ? io_in[11:7] : _io_out_T_56_rd; // @[package.scala 32:76]
  wire [4:0] _io_out_T_58_rs1 = _io_out_T_2 == 5'h1c ? io_out_s_24_rs1 : _io_out_T_56_rs1; // @[package.scala 32:76]
  wire [4:0] _io_out_T_58_rs2 = _io_out_T_2 == 5'h1c ? io_out_s_24_rs2 : _io_out_T_56_rs2; // @[package.scala 32:76]
  wire [31:0] _io_out_T_60_bits = _io_out_T_2 == 5'h1d ? io_in : _io_out_T_58_bits; // @[package.scala 32:76]
  wire [4:0] _io_out_T_60_rd = _io_out_T_2 == 5'h1d ? io_in[11:7] : _io_out_T_58_rd; // @[package.scala 32:76]
  wire [4:0] _io_out_T_60_rs1 = _io_out_T_2 == 5'h1d ? io_out_s_24_rs1 : _io_out_T_58_rs1; // @[package.scala 32:76]
  wire [4:0] _io_out_T_60_rs2 = _io_out_T_2 == 5'h1d ? io_out_s_24_rs2 : _io_out_T_58_rs2; // @[package.scala 32:76]
  wire [31:0] _io_out_T_62_bits = _io_out_T_2 == 5'h1e ? io_in : _io_out_T_60_bits; // @[package.scala 32:76]
  wire [4:0] _io_out_T_62_rd = _io_out_T_2 == 5'h1e ? io_in[11:7] : _io_out_T_60_rd; // @[package.scala 32:76]
  wire [4:0] _io_out_T_62_rs1 = _io_out_T_2 == 5'h1e ? io_out_s_24_rs1 : _io_out_T_60_rs1; // @[package.scala 32:76]
  wire [4:0] _io_out_T_62_rs2 = _io_out_T_2 == 5'h1e ? io_out_s_24_rs2 : _io_out_T_60_rs2; // @[package.scala 32:76]
  assign io_out_bits = _io_out_T_2 == 5'h1f ? io_in : _io_out_T_62_bits; // @[package.scala 32:76]
  assign io_out_rd = _io_out_T_2 == 5'h1f ? io_in[11:7] : _io_out_T_62_rd; // @[package.scala 32:76]
  assign io_out_rs1 = _io_out_T_2 == 5'h1f ? io_out_s_24_rs1 : _io_out_T_62_rs1; // @[package.scala 32:76]
  assign io_out_rs2 = _io_out_T_2 == 5'h1f ? io_out_s_24_rs2 : _io_out_T_62_rs2; // @[package.scala 32:76]
  assign io_rvc = io_in[1:0] != 2'h3; // @[RVC.scala 163:26]
endmodule
module IBuf(
  input         clock,
  input         reset,
  output        io_imem_ready,
  input         io_imem_valid,
  input  [31:0] io_imem_bits_pc,
  input  [31:0] io_imem_bits_data,
  input         io_imem_bits_xcpt_ae_inst,
  input         io_imem_bits_replay,
  input         io_kill,
  output [31:0] io_pc,
  input         io_inst_0_ready,
  output        io_inst_0_valid,
  output        io_inst_0_bits_xcpt0_ae_inst,
  output        io_inst_0_bits_xcpt1_pf_inst,
  output        io_inst_0_bits_xcpt1_gf_inst,
  output        io_inst_0_bits_xcpt1_ae_inst,
  output        io_inst_0_bits_replay,
  output        io_inst_0_bits_rvc,
  output [31:0] io_inst_0_bits_inst_bits,
  output [4:0]  io_inst_0_bits_inst_rd,
  output [4:0]  io_inst_0_bits_inst_rs1,
  output [4:0]  io_inst_0_bits_inst_rs2,
  output [31:0] io_inst_0_bits_raw
);
`ifdef RANDOMIZE_REG_INIT
  reg [31:0] _RAND_0;
  reg [31:0] _RAND_1;
  reg [31:0] _RAND_2;
  reg [31:0] _RAND_3;
  reg [31:0] _RAND_4;
`endif // RANDOMIZE_REG_INIT
  wire [31:0] exp_io_in; // @[IBuf.scala 86:21]
  wire [31:0] exp_io_out_bits; // @[IBuf.scala 86:21]
  wire [4:0] exp_io_out_rd; // @[IBuf.scala 86:21]
  wire [4:0] exp_io_out_rs1; // @[IBuf.scala 86:21]
  wire [4:0] exp_io_out_rs2; // @[IBuf.scala 86:21]
  wire  exp_io_rvc; // @[IBuf.scala 86:21]
  reg  nBufValid; // @[IBuf.scala 34:47]
  reg [31:0] buf__pc; // @[IBuf.scala 35:16]
  reg [31:0] buf__data; // @[IBuf.scala 35:16]
  reg  buf__xcpt_ae_inst; // @[IBuf.scala 35:16]
  reg  buf__replay; // @[IBuf.scala 35:16]
  wire  pcWordBits = io_imem_bits_pc[1]; // @[package.scala 154:13]
  wire [1:0] _GEN_58 = {{1'd0}, pcWordBits}; // @[IBuf.scala 41:88]
  wire [1:0] nIC = 2'h2 - _GEN_58; // @[IBuf.scala 41:88]
  wire [1:0] _nValid_T = io_imem_valid ? nIC : 2'h0; // @[IBuf.scala 43:19]
  wire [1:0] _GEN_59 = {{1'd0}, nBufValid}; // @[IBuf.scala 43:49]
  wire [1:0] nValid = _nValid_T + _GEN_59; // @[IBuf.scala 43:49]
  wire [3:0] _valid_T = 4'h1 << nValid; // @[OneHot.scala 57:35]
  wire [3:0] _valid_T_2 = _valid_T - 4'h1; // @[IBuf.scala 74:33]
  wire [1:0] valid = _valid_T_2[1:0]; // @[IBuf.scala 74:37]
  wire [1:0] _full_insn_T_2 = {{1'd0}, valid[1]}; // @[IBuf.scala 93:42]
  wire [1:0] _bufMask_T = 2'h1 << nBufValid; // @[OneHot.scala 57:35]
  wire [1:0] bufMask = _bufMask_T - 2'h1; // @[IBuf.scala 75:37]
  wire [1:0] buf_replay = buf__replay ? bufMask : 2'h0; // @[IBuf.scala 77:23]
  wire  full_insn = exp_io_rvc | _full_insn_T_2[0] | buf_replay[0]; // @[IBuf.scala 93:48]
  wire [1:0] _nReady_T_4 = exp_io_rvc ? 2'h1 : 2'h2; // @[IBuf.scala 102:71]
  wire [1:0] nReady = full_insn ? _nReady_T_4 : 2'h0; // @[IBuf.scala 102:{56,65}]
  wire [1:0] nICReady = nReady - _GEN_59; // @[IBuf.scala 42:25]
  wire  _io_imem_ready_T = nReady >= _GEN_59; // @[IBuf.scala 44:47]
  wire [1:0] _io_imem_ready_T_4 = nIC - nICReady; // @[IBuf.scala 44:92]
  wire  _io_imem_ready_T_5 = 2'h1 >= _io_imem_ready_T_4; // @[IBuf.scala 44:85]
  wire  _nBufValid_T_2 = _io_imem_ready_T | ~nBufValid; // @[package.scala 209:38]
  wire [1:0] _nBufValid_T_4 = _GEN_59 - nReady; // @[IBuf.scala 48:65]
  wire [1:0] _nBufValid_T_5 = _nBufValid_T_2 ? 2'h0 : _nBufValid_T_4; // @[IBuf.scala 48:23]
  wire [1:0] shamt = _GEN_58 + nICReady; // @[IBuf.scala 55:32]
  wire [63:0] buf_data_data = {io_imem_bits_data[31:16],io_imem_bits_data[31:16],io_imem_bits_data}; // @[Cat.scala 31:58]
  wire [5:0] _buf_data_T = {shamt, 4'h0}; // @[IBuf.scala 128:19]
  wire [63:0] _buf_data_T_1 = buf_data_data >> _buf_data_T; // @[IBuf.scala 128:10]
  wire [31:0] _buf_pc_T_1 = io_imem_bits_pc & 32'hfffffffc; // @[IBuf.scala 59:35]
  wire [2:0] _buf_pc_T_2 = {nICReady, 1'h0}; // @[IBuf.scala 59:80]
  wire [31:0] _GEN_67 = {{29'd0}, _buf_pc_T_2}; // @[IBuf.scala 59:68]
  wire [31:0] _buf_pc_T_4 = io_imem_bits_pc + _GEN_67; // @[IBuf.scala 59:68]
  wire [31:0] _buf_pc_T_5 = _buf_pc_T_4 & 32'h3; // @[IBuf.scala 59:109]
  wire [31:0] _buf_pc_T_6 = _buf_pc_T_1 | _buf_pc_T_5; // @[IBuf.scala 59:49]
  wire [1:0] _GEN_0 = io_imem_valid & _io_imem_ready_T & nICReady < nIC & _io_imem_ready_T_5 ? _io_imem_ready_T_4 :
    _nBufValid_T_5; // @[IBuf.scala 48:17 54:92 56:19]
  wire [1:0] _GEN_24 = io_inst_0_ready ? _GEN_0 : {{1'd0}, nBufValid}; // @[IBuf.scala 47:29 34:47]
  wire [1:0] _GEN_48 = io_kill ? 2'h0 : _GEN_24; // @[IBuf.scala 63:20 64:17]
  wire [1:0] _icShiftAmt_T_1 = 2'h2 + _GEN_59; // @[IBuf.scala 68:32]
  wire [1:0] icShiftAmt = _icShiftAmt_T_1 - _GEN_58; // @[IBuf.scala 68:44]
  wire [63:0] _icData_T_2 = {io_imem_bits_data,io_imem_bits_data[15:0],io_imem_bits_data[15:0]}; // @[Cat.scala 31:58]
  wire [127:0] icData_data = {_icData_T_2[63:48],_icData_T_2[63:48],_icData_T_2[63:48],_icData_T_2[63:48],
    io_imem_bits_data,io_imem_bits_data[15:0],io_imem_bits_data[15:0]}; // @[Cat.scala 31:58]
  wire [5:0] _icData_T_3 = {icShiftAmt, 4'h0}; // @[IBuf.scala 121:19]
  wire [190:0] _GEN_1 = {{63'd0}, icData_data}; // @[IBuf.scala 121:10]
  wire [190:0] _icData_T_4 = _GEN_1 << _icData_T_3; // @[IBuf.scala 121:10]
  wire [31:0] icData = _icData_T_4[95:64]; // @[package.scala 154:13]
  wire [4:0] _icMask_T_1 = {nBufValid, 4'h0}; // @[IBuf.scala 71:65]
  wire [62:0] _icMask_T_2 = 63'hffffffff << _icMask_T_1; // @[IBuf.scala 71:51]
  wire [31:0] icMask = _icMask_T_2[31:0]; // @[IBuf.scala 71:92]
  wire [31:0] _inst_T = icData & icMask; // @[IBuf.scala 72:21]
  wire [31:0] _inst_T_1 = ~icMask; // @[IBuf.scala 72:43]
  wire [31:0] _inst_T_2 = buf__data & _inst_T_1; // @[IBuf.scala 72:41]
  wire  xcpt_1_ae_inst = bufMask[1] ? buf__xcpt_ae_inst : io_imem_bits_xcpt_ae_inst; // @[IBuf.scala 76:53]
  wire [1:0] _ic_replay_T = ~bufMask; // @[IBuf.scala 78:65]
  wire [1:0] _ic_replay_T_1 = valid & _ic_replay_T; // @[IBuf.scala 78:63]
  wire [1:0] _ic_replay_T_2 = io_imem_bits_replay ? _ic_replay_T_1 : 2'h0; // @[IBuf.scala 78:35]
  wire [1:0] ic_replay = buf_replay | _ic_replay_T_2; // @[IBuf.scala 78:30]
  wire [1:0] _replay_T_5 = {{1'd0}, ic_replay[1]}; // @[IBuf.scala 92:61]
  wire [2:0] _io_inst_0_bits_xcpt1_T_4 = {2'h0,xcpt_1_ae_inst}; // @[IBuf.scala 96:63]
  wire [2:0] _io_inst_0_bits_xcpt1_T_5 = exp_io_rvc ? 3'h0 : _io_inst_0_bits_xcpt1_T_4; // @[IBuf.scala 96:35]
  RVCExpander exp ( // @[IBuf.scala 86:21]
    .io_in(exp_io_in),
    .io_out_bits(exp_io_out_bits),
    .io_out_rd(exp_io_out_rd),
    .io_out_rs1(exp_io_out_rs1),
    .io_out_rs2(exp_io_out_rs2),
    .io_rvc(exp_io_rvc)
  );
  assign io_imem_ready = io_inst_0_ready & nReady >= _GEN_59 & (nICReady >= nIC | 2'h1 >= _io_imem_ready_T_4); // @[IBuf.scala 44:60]
  assign io_pc = nBufValid > 1'h0 ? buf__pc : io_imem_bits_pc; // @[IBuf.scala 82:15]
  assign io_inst_0_valid = valid[0] & full_insn; // @[IBuf.scala 94:36]
  assign io_inst_0_bits_xcpt0_ae_inst = bufMask[0] ? buf__xcpt_ae_inst : io_imem_bits_xcpt_ae_inst; // @[IBuf.scala 76:53]
  assign io_inst_0_bits_xcpt1_pf_inst = _io_inst_0_bits_xcpt1_T_5[2]; // @[IBuf.scala 96:79]
  assign io_inst_0_bits_xcpt1_gf_inst = _io_inst_0_bits_xcpt1_T_5[1]; // @[IBuf.scala 96:79]
  assign io_inst_0_bits_xcpt1_ae_inst = _io_inst_0_bits_xcpt1_T_5[0]; // @[IBuf.scala 96:79]
  assign io_inst_0_bits_replay = ic_replay[0] | ~exp_io_rvc & _replay_T_5[0]; // @[IBuf.scala 92:33]
  assign io_inst_0_bits_rvc = exp_io_rvc; // @[IBuf.scala 98:27]
  assign io_inst_0_bits_inst_bits = exp_io_out_bits; // @[IBuf.scala 88:26]
  assign io_inst_0_bits_inst_rd = exp_io_out_rd; // @[IBuf.scala 88:26]
  assign io_inst_0_bits_inst_rs1 = exp_io_out_rs1; // @[IBuf.scala 88:26]
  assign io_inst_0_bits_inst_rs2 = exp_io_out_rs2; // @[IBuf.scala 88:26]
  assign io_inst_0_bits_raw = _inst_T | _inst_T_2; // @[IBuf.scala 72:30]
  assign exp_io_in = _inst_T | _inst_T_2; // @[IBuf.scala 72:30]
  always @(posedge clock) begin
    if (reset) begin // @[IBuf.scala 34:47]
      nBufValid <= 1'h0; // @[IBuf.scala 34:47]
    end else begin
      nBufValid <= _GEN_48[0];
    end
    if (io_inst_0_ready) begin // @[IBuf.scala 47:29]
      if (io_imem_valid & _io_imem_ready_T & nICReady < nIC & _io_imem_ready_T_5) begin // @[IBuf.scala 54:92]
        buf__pc <= _buf_pc_T_6; // @[IBuf.scala 59:16]
      end
    end
    if (io_inst_0_ready) begin // @[IBuf.scala 47:29]
      if (io_imem_valid & _io_imem_ready_T & nICReady < nIC & _io_imem_ready_T_5) begin // @[IBuf.scala 54:92]
        buf__data <= {{16'd0}, _buf_data_T_1[15:0]}; // @[IBuf.scala 58:18]
      end
    end
    if (io_inst_0_ready) begin // @[IBuf.scala 47:29]
      if (io_imem_valid & _io_imem_ready_T & nICReady < nIC & _io_imem_ready_T_5) begin // @[IBuf.scala 54:92]
        buf__xcpt_ae_inst <= io_imem_bits_xcpt_ae_inst; // @[IBuf.scala 57:13]
      end
    end
    if (io_inst_0_ready) begin // @[IBuf.scala 47:29]
      if (io_imem_valid & _io_imem_ready_T & nICReady < nIC & _io_imem_ready_T_5) begin // @[IBuf.scala 54:92]
        buf__replay <= io_imem_bits_replay; // @[IBuf.scala 57:13]
      end
    end
  end
// Register and memory initialization
`ifdef RANDOMIZE_GARBAGE_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_INVALID_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_REG_INIT
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_MEM_INIT
`define RANDOMIZE
`endif
`ifndef RANDOM
`define RANDOM $random
`endif
`ifdef RANDOMIZE_MEM_INIT
  integer initvar;
`endif
`ifndef SYNTHESIS
`ifdef FIRRTL_BEFORE_INITIAL
`FIRRTL_BEFORE_INITIAL
`endif
initial begin
  `ifdef RANDOMIZE
    `ifdef INIT_RANDOM
      `INIT_RANDOM
    `endif
    `ifndef VERILATOR
      `ifdef RANDOMIZE_DELAY
        #`RANDOMIZE_DELAY begin end
      `else
        #0.002 begin end
      `endif
    `endif
`ifdef RANDOMIZE_REG_INIT
  _RAND_0 = {1{`RANDOM}};
  nBufValid = _RAND_0[0:0];
  _RAND_1 = {1{`RANDOM}};
  buf__pc = _RAND_1[31:0];
  _RAND_2 = {1{`RANDOM}};
  buf__data = _RAND_2[31:0];
  _RAND_3 = {1{`RANDOM}};
  buf__xcpt_ae_inst = _RAND_3[0:0];
  _RAND_4 = {1{`RANDOM}};
  buf__replay = _RAND_4[0:0];
`endif // RANDOMIZE_REG_INIT
  `endif // RANDOMIZE
end // initial
`ifdef FIRRTL_AFTER_INITIAL
`FIRRTL_AFTER_INITIAL
`endif
`endif // SYNTHESIS
endmodule
module CSRFile(
  input         clock,
  input         reset,
  input         io_ungated_clock,
  input         io_interrupts_debug,
  input         io_interrupts_mtip,
  input         io_interrupts_msip,
  input         io_interrupts_meip,
  input         io_hartid,
  input  [11:0] io_rw_addr,
  input  [2:0]  io_rw_cmd,
  output [31:0] io_rw_rdata,
  input  [31:0] io_rw_wdata,
  input  [31:0] io_decode_0_inst,
  output        io_decode_0_fp_illegal,
  output        io_decode_0_fp_csr,
  output        io_decode_0_rocc_illegal,
  output        io_decode_0_read_illegal,
  output        io_decode_0_write_illegal,
  output        io_decode_0_write_flush,
  output        io_decode_0_system_illegal,
  output        io_csr_stall,
  output        io_eret,
  output        io_singleStep,
  output        io_status_debug,
  output        io_status_cease,
  output        io_status_wfi,
  output [31:0] io_status_isa,
  output [1:0]  io_status_dprv,
  output        io_status_dv,
  output [1:0]  io_status_prv,
  output        io_status_v,
  output        io_status_sd,
  output [22:0] io_status_zero2,
  output        io_status_mpv,
  output        io_status_gva,
  output        io_status_mbe,
  output        io_status_sbe,
  output [1:0]  io_status_sxl,
  output [1:0]  io_status_uxl,
  output        io_status_sd_rv32,
  output [7:0]  io_status_zero1,
  output        io_status_tsr,
  output        io_status_tw,
  output        io_status_tvm,
  output        io_status_mxr,
  output        io_status_sum,
  output        io_status_mprv,
  output [1:0]  io_status_xs,
  output [1:0]  io_status_fs,
  output [1:0]  io_status_mpp,
  output [1:0]  io_status_vs,
  output        io_status_spp,
  output        io_status_mpie,
  output        io_status_ube,
  output        io_status_spie,
  output        io_status_upie,
  output        io_status_mie,
  output        io_status_hie,
  output        io_status_sie,
  output        io_status_uie,
  output [31:0] io_evec,
  input         io_exception,
  input         io_retire,
  input  [31:0] io_cause,
  input  [31:0] io_pc,
  input  [31:0] io_tval,
  input         io_gva,
  output [31:0] io_time,
  output        io_interrupt,
  output [31:0] io_interrupt_cause,
  output        io_bp_0_control_action,
  output [1:0]  io_bp_0_control_tmatch,
  output        io_bp_0_control_x,
  output        io_bp_0_control_w,
  output        io_bp_0_control_r,
  output [31:0] io_bp_0_address,
  output        io_pmp_0_cfg_l,
  output [1:0]  io_pmp_0_cfg_a,
  output        io_pmp_0_cfg_x,
  output        io_pmp_0_cfg_w,
  output        io_pmp_0_cfg_r,
  output [29:0] io_pmp_0_addr,
  output [31:0] io_pmp_0_mask,
  output        io_pmp_1_cfg_l,
  output [1:0]  io_pmp_1_cfg_a,
  output        io_pmp_1_cfg_x,
  output        io_pmp_1_cfg_w,
  output        io_pmp_1_cfg_r,
  output [29:0] io_pmp_1_addr,
  output [31:0] io_pmp_1_mask,
  output        io_pmp_2_cfg_l,
  output [1:0]  io_pmp_2_cfg_a,
  output        io_pmp_2_cfg_x,
  output        io_pmp_2_cfg_w,
  output        io_pmp_2_cfg_r,
  output [29:0] io_pmp_2_addr,
  output [31:0] io_pmp_2_mask,
  output        io_pmp_3_cfg_l,
  output [1:0]  io_pmp_3_cfg_a,
  output        io_pmp_3_cfg_x,
  output        io_pmp_3_cfg_w,
  output        io_pmp_3_cfg_r,
  output [29:0] io_pmp_3_addr,
  output [31:0] io_pmp_3_mask,
  output        io_pmp_4_cfg_l,
  output [1:0]  io_pmp_4_cfg_a,
  output        io_pmp_4_cfg_x,
  output        io_pmp_4_cfg_w,
  output        io_pmp_4_cfg_r,
  output [29:0] io_pmp_4_addr,
  output [31:0] io_pmp_4_mask,
  output        io_pmp_5_cfg_l,
  output [1:0]  io_pmp_5_cfg_a,
  output        io_pmp_5_cfg_x,
  output        io_pmp_5_cfg_w,
  output        io_pmp_5_cfg_r,
  output [29:0] io_pmp_5_addr,
  output [31:0] io_pmp_5_mask,
  output        io_pmp_6_cfg_l,
  output [1:0]  io_pmp_6_cfg_a,
  output        io_pmp_6_cfg_x,
  output        io_pmp_6_cfg_w,
  output        io_pmp_6_cfg_r,
  output [29:0] io_pmp_6_addr,
  output [31:0] io_pmp_6_mask,
  output        io_pmp_7_cfg_l,
  output [1:0]  io_pmp_7_cfg_a,
  output        io_pmp_7_cfg_x,
  output        io_pmp_7_cfg_w,
  output        io_pmp_7_cfg_r,
  output [29:0] io_pmp_7_addr,
  output [31:0] io_pmp_7_mask,
  output        io_inhibit_cycle,
  input  [31:0] io_inst_0,
  output        io_trace_0_valid,
  output [31:0] io_trace_0_iaddr,
  output [31:0] io_trace_0_insn,
  output        io_trace_0_exception,
  output [31:0] io_customCSRs_0_value
);
`ifdef RANDOMIZE_REG_INIT
  reg [31:0] _RAND_0;
  reg [31:0] _RAND_1;
  reg [31:0] _RAND_2;
  reg [31:0] _RAND_3;
  reg [31:0] _RAND_4;
  reg [31:0] _RAND_5;
  reg [31:0] _RAND_6;
  reg [31:0] _RAND_7;
  reg [31:0] _RAND_8;
  reg [31:0] _RAND_9;
  reg [31:0] _RAND_10;
  reg [31:0] _RAND_11;
  reg [31:0] _RAND_12;
  reg [31:0] _RAND_13;
  reg [31:0] _RAND_14;
  reg [31:0] _RAND_15;
  reg [31:0] _RAND_16;
  reg [31:0] _RAND_17;
  reg [31:0] _RAND_18;
  reg [31:0] _RAND_19;
  reg [31:0] _RAND_20;
  reg [31:0] _RAND_21;
  reg [31:0] _RAND_22;
  reg [31:0] _RAND_23;
  reg [31:0] _RAND_24;
  reg [31:0] _RAND_25;
  reg [31:0] _RAND_26;
  reg [31:0] _RAND_27;
  reg [31:0] _RAND_28;
  reg [31:0] _RAND_29;
  reg [31:0] _RAND_30;
  reg [31:0] _RAND_31;
  reg [31:0] _RAND_32;
  reg [31:0] _RAND_33;
  reg [31:0] _RAND_34;
  reg [31:0] _RAND_35;
  reg [31:0] _RAND_36;
  reg [31:0] _RAND_37;
  reg [31:0] _RAND_38;
  reg [31:0] _RAND_39;
  reg [31:0] _RAND_40;
  reg [31:0] _RAND_41;
  reg [31:0] _RAND_42;
  reg [31:0] _RAND_43;
  reg [31:0] _RAND_44;
  reg [31:0] _RAND_45;
  reg [31:0] _RAND_46;
  reg [31:0] _RAND_47;
  reg [31:0] _RAND_48;
  reg [31:0] _RAND_49;
  reg [31:0] _RAND_50;
  reg [31:0] _RAND_51;
  reg [31:0] _RAND_52;
  reg [31:0] _RAND_53;
  reg [31:0] _RAND_54;
  reg [31:0] _RAND_55;
  reg [31:0] _RAND_56;
  reg [31:0] _RAND_57;
  reg [31:0] _RAND_58;
  reg [31:0] _RAND_59;
  reg [31:0] _RAND_60;
  reg [31:0] _RAND_61;
  reg [31:0] _RAND_62;
  reg [31:0] _RAND_63;
  reg [31:0] _RAND_64;
  reg [31:0] _RAND_65;
  reg [31:0] _RAND_66;
  reg [31:0] _RAND_67;
  reg [31:0] _RAND_68;
  reg [31:0] _RAND_69;
  reg [31:0] _RAND_70;
  reg [31:0] _RAND_71;
  reg [31:0] _RAND_72;
  reg [31:0] _RAND_73;
  reg [31:0] _RAND_74;
  reg [63:0] _RAND_75;
  reg [31:0] _RAND_76;
  reg [63:0] _RAND_77;
  reg [31:0] _RAND_78;
  reg [31:0] _RAND_79;
  reg [31:0] _RAND_80;
`endif // RANDOMIZE_REG_INIT
  reg  reg_mstatus_gva; // @[CSR.scala 370:24]
  reg  reg_mstatus_spp; // @[CSR.scala 370:24]
  reg  reg_mstatus_mpie; // @[CSR.scala 370:24]
  reg  reg_mstatus_mie; // @[CSR.scala 370:24]
  reg  reg_dcsr_ebreakm; // @[CSR.scala 378:21]
  reg [2:0] reg_dcsr_cause; // @[CSR.scala 378:21]
  reg  reg_dcsr_step; // @[CSR.scala 378:21]
  reg  reg_debug; // @[CSR.scala 450:22]
  reg [31:0] reg_dpc; // @[CSR.scala 451:20]
  reg [31:0] reg_dscratch0; // @[CSR.scala 452:26]
  reg  reg_singleStepped; // @[CSR.scala 454:30]
  reg  reg_bp_0_control_dmode; // @[CSR.scala 460:19]
  reg  reg_bp_0_control_action; // @[CSR.scala 460:19]
  reg [1:0] reg_bp_0_control_tmatch; // @[CSR.scala 460:19]
  reg  reg_bp_0_control_x; // @[CSR.scala 460:19]
  reg  reg_bp_0_control_w; // @[CSR.scala 460:19]
  reg  reg_bp_0_control_r; // @[CSR.scala 460:19]
  reg [31:0] reg_bp_0_address; // @[CSR.scala 460:19]
  reg  reg_pmp_0_cfg_l; // @[CSR.scala 461:20]
  reg [1:0] reg_pmp_0_cfg_a; // @[CSR.scala 461:20]
  reg  reg_pmp_0_cfg_x; // @[CSR.scala 461:20]
  reg  reg_pmp_0_cfg_w; // @[CSR.scala 461:20]
  reg  reg_pmp_0_cfg_r; // @[CSR.scala 461:20]
  reg [29:0] reg_pmp_0_addr; // @[CSR.scala 461:20]
  reg  reg_pmp_1_cfg_l; // @[CSR.scala 461:20]
  reg [1:0] reg_pmp_1_cfg_a; // @[CSR.scala 461:20]
  reg  reg_pmp_1_cfg_x; // @[CSR.scala 461:20]
  reg  reg_pmp_1_cfg_w; // @[CSR.scala 461:20]
  reg  reg_pmp_1_cfg_r; // @[CSR.scala 461:20]
  reg [29:0] reg_pmp_1_addr; // @[CSR.scala 461:20]
  reg  reg_pmp_2_cfg_l; // @[CSR.scala 461:20]
  reg [1:0] reg_pmp_2_cfg_a; // @[CSR.scala 461:20]
  reg  reg_pmp_2_cfg_x; // @[CSR.scala 461:20]
  reg  reg_pmp_2_cfg_w; // @[CSR.scala 461:20]
  reg  reg_pmp_2_cfg_r; // @[CSR.scala 461:20]
  reg [29:0] reg_pmp_2_addr; // @[CSR.scala 461:20]
  reg  reg_pmp_3_cfg_l; // @[CSR.scala 461:20]
  reg [1:0] reg_pmp_3_cfg_a; // @[CSR.scala 461:20]
  reg  reg_pmp_3_cfg_x; // @[CSR.scala 461:20]
  reg  reg_pmp_3_cfg_w; // @[CSR.scala 461:20]
  reg  reg_pmp_3_cfg_r; // @[CSR.scala 461:20]
  reg [29:0] reg_pmp_3_addr; // @[CSR.scala 461:20]
  reg  reg_pmp_4_cfg_l; // @[CSR.scala 461:20]
  reg [1:0] reg_pmp_4_cfg_a; // @[CSR.scala 461:20]
  reg  reg_pmp_4_cfg_x; // @[CSR.scala 461:20]
  reg  reg_pmp_4_cfg_w; // @[CSR.scala 461:20]
  reg  reg_pmp_4_cfg_r; // @[CSR.scala 461:20]
  reg [29:0] reg_pmp_4_addr; // @[CSR.scala 461:20]
  reg  reg_pmp_5_cfg_l; // @[CSR.scala 461:20]
  reg [1:0] reg_pmp_5_cfg_a; // @[CSR.scala 461:20]
  reg  reg_pmp_5_cfg_x; // @[CSR.scala 461:20]
  reg  reg_pmp_5_cfg_w; // @[CSR.scala 461:20]
  reg  reg_pmp_5_cfg_r; // @[CSR.scala 461:20]
  reg [29:0] reg_pmp_5_addr; // @[CSR.scala 461:20]
  reg  reg_pmp_6_cfg_l; // @[CSR.scala 461:20]
  reg [1:0] reg_pmp_6_cfg_a; // @[CSR.scala 461:20]
  reg  reg_pmp_6_cfg_x; // @[CSR.scala 461:20]
  reg  reg_pmp_6_cfg_w; // @[CSR.scala 461:20]
  reg  reg_pmp_6_cfg_r; // @[CSR.scala 461:20]
  reg [29:0] reg_pmp_6_addr; // @[CSR.scala 461:20]
  reg  reg_pmp_7_cfg_l; // @[CSR.scala 461:20]
  reg [1:0] reg_pmp_7_cfg_a; // @[CSR.scala 461:20]
  reg  reg_pmp_7_cfg_x; // @[CSR.scala 461:20]
  reg  reg_pmp_7_cfg_w; // @[CSR.scala 461:20]
  reg  reg_pmp_7_cfg_r; // @[CSR.scala 461:20]
  reg [29:0] reg_pmp_7_addr; // @[CSR.scala 461:20]
  reg [31:0] reg_mie; // @[CSR.scala 463:20]
  reg [31:0] reg_mepc; // @[CSR.scala 473:21]
  reg [31:0] reg_mcause; // @[CSR.scala 474:27]
  reg [31:0] reg_mtval; // @[CSR.scala 475:22]
  reg [31:0] reg_mscratch; // @[CSR.scala 477:25]
  reg [31:0] reg_mtvec; // @[CSR.scala 480:27]
  reg  reg_wfi; // @[CSR.scala 539:50]
  reg [2:0] reg_mcountinhibit; // @[CSR.scala 548:34]
  wire  x79 = reg_mcountinhibit[2]; // @[CSR.scala 550:75]
  reg [5:0] small_; // @[Counters.scala 45:37]
  wire [5:0] _GEN_34 = {{5'd0}, io_retire}; // @[Counters.scala 46:33]
  wire [6:0] nextSmall = small_ + _GEN_34; // @[Counters.scala 46:33]
  wire  _T_14 = ~x79; // @[Counters.scala 47:9]
  wire [6:0] _GEN_0 = ~x79 ? nextSmall : {{1'd0}, small_}; // @[Counters.scala 47:{19,27} 45:37]
  reg [57:0] large_; // @[Counters.scala 50:27]
  wire [57:0] _large_r_T_1 = large_ + 58'h1; // @[Counters.scala 51:55]
  wire [57:0] _GEN_1 = nextSmall[6] & _T_14 ? _large_r_T_1 : large_; // @[Counters.scala 50:27 51:{46,50}]
  wire [63:0] value = {large_,small_}; // @[Cat.scala 31:58]
  wire  x86 = ~io_csr_stall; // @[CSR.scala 552:56]
  reg [5:0] small_1; // @[Counters.scala 45:37]
  wire [5:0] _GEN_35 = {{5'd0}, x86}; // @[Counters.scala 46:33]
  wire [6:0] nextSmall_1 = small_1 + _GEN_35; // @[Counters.scala 46:33]
  wire  _T_15 = ~reg_mcountinhibit[0]; // @[Counters.scala 47:9]
  wire [6:0] _GEN_2 = ~reg_mcountinhibit[0] ? nextSmall_1 : {{1'd0}, small_1}; // @[Counters.scala 47:{19,27} 45:37]
  reg [57:0] large_1; // @[Counters.scala 50:27]
  wire [57:0] _large_r_T_3 = large_1 + 58'h1; // @[Counters.scala 51:55]
  wire [57:0] _GEN_3 = nextSmall_1[6] & _T_15 ? _large_r_T_3 : large_1; // @[Counters.scala 50:27 51:{46,50}]
  wire [63:0] value_1 = {large_1,small_1}; // @[Cat.scala 31:58]
  wire [15:0] _read_mip_T = {4'h0,io_interrupts_meip,1'h0,2'h0,io_interrupts_mtip,1'h0,2'h0,io_interrupts_msip,1'h0,2'h0
    }; // @[CSR.scala 568:22]
  wire [15:0] read_mip = _read_mip_T & 16'h888; // @[CSR.scala 568:29]
  wire [31:0] _GEN_40 = {{16'd0}, read_mip}; // @[CSR.scala 572:56]
  wire [31:0] pending_interrupts = _GEN_40 & reg_mie; // @[CSR.scala 572:56]
  wire [14:0] d_interrupts = {io_interrupts_debug, 14'h0}; // @[CSR.scala 573:42]
  wire [31:0] _m_interrupts_T_3 = ~pending_interrupts; // @[CSR.scala 578:83]
  wire [31:0] _m_interrupts_T_5 = ~_m_interrupts_T_3; // @[CSR.scala 578:81]
  wire [31:0] m_interrupts = reg_mstatus_mie ? _m_interrupts_T_5 : 32'h0; // @[CSR.scala 578:25]
  wire  _any_T_78 = d_interrupts[14] | d_interrupts[13] | d_interrupts[12] | d_interrupts[11] | d_interrupts[3] |
    d_interrupts[7] | d_interrupts[9] | d_interrupts[1] | d_interrupts[5] | d_interrupts[10] | d_interrupts[2] |
    d_interrupts[6] | d_interrupts[8] | d_interrupts[0] | d_interrupts[4] | m_interrupts[15]; // @[CSR.scala 1537:90]
  wire  anyInterrupt = _any_T_78 | m_interrupts[14] | m_interrupts[13] | m_interrupts[12] | m_interrupts[11] |
    m_interrupts[3] | m_interrupts[7] | m_interrupts[9] | m_interrupts[1] | m_interrupts[5] | m_interrupts[10] |
    m_interrupts[2] | m_interrupts[6] | m_interrupts[8] | m_interrupts[0] | m_interrupts[4]; // @[CSR.scala 1537:90]
  wire [3:0] _which_T_95 = m_interrupts[0] ? 4'h0 : 4'h4; // @[Mux.scala 47:70]
  wire [3:0] _which_T_96 = m_interrupts[8] ? 4'h8 : _which_T_95; // @[Mux.scala 47:70]
  wire [3:0] _which_T_97 = m_interrupts[6] ? 4'h6 : _which_T_96; // @[Mux.scala 47:70]
  wire [3:0] _which_T_98 = m_interrupts[2] ? 4'h2 : _which_T_97; // @[Mux.scala 47:70]
  wire [3:0] _which_T_99 = m_interrupts[10] ? 4'ha : _which_T_98; // @[Mux.scala 47:70]
  wire [3:0] _which_T_100 = m_interrupts[5] ? 4'h5 : _which_T_99; // @[Mux.scala 47:70]
  wire [3:0] _which_T_101 = m_interrupts[1] ? 4'h1 : _which_T_100; // @[Mux.scala 47:70]
  wire [3:0] _which_T_102 = m_interrupts[9] ? 4'h9 : _which_T_101; // @[Mux.scala 47:70]
  wire [3:0] _which_T_103 = m_interrupts[7] ? 4'h7 : _which_T_102; // @[Mux.scala 47:70]
  wire [3:0] _which_T_104 = m_interrupts[3] ? 4'h3 : _which_T_103; // @[Mux.scala 47:70]
  wire [3:0] _which_T_105 = m_interrupts[11] ? 4'hb : _which_T_104; // @[Mux.scala 47:70]
  wire [3:0] _which_T_106 = m_interrupts[12] ? 4'hc : _which_T_105; // @[Mux.scala 47:70]
  wire [3:0] _which_T_107 = m_interrupts[13] ? 4'hd : _which_T_106; // @[Mux.scala 47:70]
  wire [3:0] _which_T_108 = m_interrupts[14] ? 4'he : _which_T_107; // @[Mux.scala 47:70]
  wire [3:0] _which_T_109 = m_interrupts[15] ? 4'hf : _which_T_108; // @[Mux.scala 47:70]
  wire [3:0] _which_T_111 = d_interrupts[4] ? 4'h4 : _which_T_109; // @[Mux.scala 47:70]
  wire [3:0] _which_T_112 = d_interrupts[0] ? 4'h0 : _which_T_111; // @[Mux.scala 47:70]
  wire [3:0] _which_T_113 = d_interrupts[8] ? 4'h8 : _which_T_112; // @[Mux.scala 47:70]
  wire [3:0] _which_T_114 = d_interrupts[6] ? 4'h6 : _which_T_113; // @[Mux.scala 47:70]
  wire [3:0] _which_T_115 = d_interrupts[2] ? 4'h2 : _which_T_114; // @[Mux.scala 47:70]
  wire [3:0] _which_T_116 = d_interrupts[10] ? 4'ha : _which_T_115; // @[Mux.scala 47:70]
  wire [3:0] _which_T_117 = d_interrupts[5] ? 4'h5 : _which_T_116; // @[Mux.scala 47:70]
  wire [3:0] _which_T_118 = d_interrupts[1] ? 4'h1 : _which_T_117; // @[Mux.scala 47:70]
  wire [3:0] _which_T_119 = d_interrupts[9] ? 4'h9 : _which_T_118; // @[Mux.scala 47:70]
  wire [3:0] _which_T_120 = d_interrupts[7] ? 4'h7 : _which_T_119; // @[Mux.scala 47:70]
  wire [3:0] _which_T_121 = d_interrupts[3] ? 4'h3 : _which_T_120; // @[Mux.scala 47:70]
  wire [3:0] _which_T_122 = d_interrupts[11] ? 4'hb : _which_T_121; // @[Mux.scala 47:70]
  wire [3:0] _which_T_123 = d_interrupts[12] ? 4'hc : _which_T_122; // @[Mux.scala 47:70]
  wire [3:0] _which_T_124 = d_interrupts[13] ? 4'hd : _which_T_123; // @[Mux.scala 47:70]
  wire [3:0] whichInterrupt = d_interrupts[14] ? 4'he : _which_T_124; // @[Mux.scala 47:70]
  wire [31:0] _GEN_41 = {{28'd0}, whichInterrupt}; // @[CSR.scala 583:67]
  wire  _io_interrupt_T = ~io_singleStep; // @[CSR.scala 584:36]
  wire [30:0] pmp_mask_base = {reg_pmp_0_addr,reg_pmp_0_cfg_a[0]}; // @[Cat.scala 31:58]
  wire [30:0] _pmp_mask_T_1 = pmp_mask_base + 31'h1; // @[PMP.scala 58:23]
  wire [30:0] _pmp_mask_T_2 = ~_pmp_mask_T_1; // @[PMP.scala 58:16]
  wire [30:0] _pmp_mask_T_3 = pmp_mask_base & _pmp_mask_T_2; // @[PMP.scala 58:14]
  wire [32:0] _pmp_mask_T_4 = {_pmp_mask_T_3,2'h3}; // @[Cat.scala 31:58]
  wire [30:0] pmp_mask_base_1 = {reg_pmp_1_addr,reg_pmp_1_cfg_a[0]}; // @[Cat.scala 31:58]
  wire [30:0] _pmp_mask_T_6 = pmp_mask_base_1 + 31'h1; // @[PMP.scala 58:23]
  wire [30:0] _pmp_mask_T_7 = ~_pmp_mask_T_6; // @[PMP.scala 58:16]
  wire [30:0] _pmp_mask_T_8 = pmp_mask_base_1 & _pmp_mask_T_7; // @[PMP.scala 58:14]
  wire [32:0] _pmp_mask_T_9 = {_pmp_mask_T_8,2'h3}; // @[Cat.scala 31:58]
  wire [30:0] pmp_mask_base_2 = {reg_pmp_2_addr,reg_pmp_2_cfg_a[0]}; // @[Cat.scala 31:58]
  wire [30:0] _pmp_mask_T_11 = pmp_mask_base_2 + 31'h1; // @[PMP.scala 58:23]
  wire [30:0] _pmp_mask_T_12 = ~_pmp_mask_T_11; // @[PMP.scala 58:16]
  wire [30:0] _pmp_mask_T_13 = pmp_mask_base_2 & _pmp_mask_T_12; // @[PMP.scala 58:14]
  wire [32:0] _pmp_mask_T_14 = {_pmp_mask_T_13,2'h3}; // @[Cat.scala 31:58]
  wire [30:0] pmp_mask_base_3 = {reg_pmp_3_addr,reg_pmp_3_cfg_a[0]}; // @[Cat.scala 31:58]
  wire [30:0] _pmp_mask_T_16 = pmp_mask_base_3 + 31'h1; // @[PMP.scala 58:23]
  wire [30:0] _pmp_mask_T_17 = ~_pmp_mask_T_16; // @[PMP.scala 58:16]
  wire [30:0] _pmp_mask_T_18 = pmp_mask_base_3 & _pmp_mask_T_17; // @[PMP.scala 58:14]
  wire [32:0] _pmp_mask_T_19 = {_pmp_mask_T_18,2'h3}; // @[Cat.scala 31:58]
  wire [30:0] pmp_mask_base_4 = {reg_pmp_4_addr,reg_pmp_4_cfg_a[0]}; // @[Cat.scala 31:58]
  wire [30:0] _pmp_mask_T_21 = pmp_mask_base_4 + 31'h1; // @[PMP.scala 58:23]
  wire [30:0] _pmp_mask_T_22 = ~_pmp_mask_T_21; // @[PMP.scala 58:16]
  wire [30:0] _pmp_mask_T_23 = pmp_mask_base_4 & _pmp_mask_T_22; // @[PMP.scala 58:14]
  wire [32:0] _pmp_mask_T_24 = {_pmp_mask_T_23,2'h3}; // @[Cat.scala 31:58]
  wire [30:0] pmp_mask_base_5 = {reg_pmp_5_addr,reg_pmp_5_cfg_a[0]}; // @[Cat.scala 31:58]
  wire [30:0] _pmp_mask_T_26 = pmp_mask_base_5 + 31'h1; // @[PMP.scala 58:23]
  wire [30:0] _pmp_mask_T_27 = ~_pmp_mask_T_26; // @[PMP.scala 58:16]
  wire [30:0] _pmp_mask_T_28 = pmp_mask_base_5 & _pmp_mask_T_27; // @[PMP.scala 58:14]
  wire [32:0] _pmp_mask_T_29 = {_pmp_mask_T_28,2'h3}; // @[Cat.scala 31:58]
  wire [30:0] pmp_mask_base_6 = {reg_pmp_6_addr,reg_pmp_6_cfg_a[0]}; // @[Cat.scala 31:58]
  wire [30:0] _pmp_mask_T_31 = pmp_mask_base_6 + 31'h1; // @[PMP.scala 58:23]
  wire [30:0] _pmp_mask_T_32 = ~_pmp_mask_T_31; // @[PMP.scala 58:16]
  wire [30:0] _pmp_mask_T_33 = pmp_mask_base_6 & _pmp_mask_T_32; // @[PMP.scala 58:14]
  wire [32:0] _pmp_mask_T_34 = {_pmp_mask_T_33,2'h3}; // @[Cat.scala 31:58]
  wire [30:0] pmp_mask_base_7 = {reg_pmp_7_addr,reg_pmp_7_cfg_a[0]}; // @[Cat.scala 31:58]
  wire [30:0] _pmp_mask_T_36 = pmp_mask_base_7 + 31'h1; // @[PMP.scala 58:23]
  wire [30:0] _pmp_mask_T_37 = ~_pmp_mask_T_36; // @[PMP.scala 58:16]
  wire [30:0] _pmp_mask_T_38 = pmp_mask_base_7 & _pmp_mask_T_37; // @[PMP.scala 58:14]
  wire [32:0] _pmp_mask_T_39 = {_pmp_mask_T_38,2'h3}; // @[Cat.scala 31:58]
  reg [31:0] reg_misa; // @[CSR.scala 606:21]
  wire [8:0] read_mstatus_lo_lo = {io_status_spp,io_status_mpie,io_status_ube,io_status_spie,io_status_upie,
    io_status_mie,io_status_hie,io_status_sie,io_status_uie}; // @[CSR.scala 607:38]
  wire [21:0] read_mstatus_lo = {io_status_tw,io_status_tvm,io_status_mxr,io_status_sum,io_status_mprv,io_status_xs,
    io_status_fs,io_status_mpp,io_status_vs,read_mstatus_lo_lo}; // @[CSR.scala 607:38]
  wire [64:0] read_mstatus_hi_hi = {io_status_debug,io_status_cease,io_status_wfi,io_status_isa,io_status_dprv,
    io_status_dv,io_status_prv,io_status_v,io_status_sd,io_status_zero2}; // @[CSR.scala 607:38]
  wire [82:0] read_mstatus_hi = {read_mstatus_hi_hi,io_status_mpv,io_status_gva,io_status_mbe,io_status_sbe,
    io_status_sxl,io_status_uxl,io_status_sd_rv32,io_status_zero1,io_status_tsr}; // @[CSR.scala 607:38]
  wire [104:0] _read_mstatus_T = {read_mstatus_hi,read_mstatus_lo}; // @[CSR.scala 607:38]
  wire [31:0] read_mstatus = _read_mstatus_T[31:0]; // @[CSR.scala 607:40]
  wire [6:0] _read_mtvec_T_1 = reg_mtvec[0] ? 7'h7e : 7'h2; // @[CSR.scala 1566:39]
  wire [31:0] _read_mtvec_T_3 = {{25'd0}, _read_mtvec_T_1}; // @[package.scala 165:41]
  wire [31:0] _read_mtvec_T_4 = ~_read_mtvec_T_3; // @[package.scala 165:37]
  wire [31:0] read_mtvec = reg_mtvec & _read_mtvec_T_4; // @[package.scala 165:35]
  wire [6:0] lo_4 = {4'h8,reg_bp_0_control_x,reg_bp_0_control_w,reg_bp_0_control_r}; // @[CSR.scala 613:48]
  wire [31:0] _T_16 = {4'h2,reg_bp_0_control_dmode,14'h400,reg_bp_0_control_action,1'h0,2'h0,reg_bp_0_control_tmatch,
    lo_4}; // @[CSR.scala 613:48]
  wire [31:0] _T_18 = ~reg_mepc; // @[CSR.scala 1565:28]
  wire [1:0] _T_20 = reg_misa[2] ? 2'h1 : 2'h3; // @[CSR.scala 1565:36]
  wire [31:0] _GEN_586 = {{30'd0}, _T_20}; // @[CSR.scala 1565:31]
  wire [31:0] _T_21 = _T_18 | _GEN_586; // @[CSR.scala 1565:31]
  wire [31:0] _T_22 = ~_T_21; // @[CSR.scala 1565:26]
  wire [31:0] _T_23 = {4'h4,12'h0,reg_dcsr_ebreakm,4'h0,2'h0,reg_dcsr_cause,1'h0,2'h0,reg_dcsr_step,2'h3}; // @[CSR.scala 628:27]
  wire [31:0] _T_24 = ~reg_dpc; // @[CSR.scala 1565:28]
  wire [31:0] _T_27 = _T_24 | _GEN_586; // @[CSR.scala 1565:31]
  wire [31:0] _T_28 = ~_T_27; // @[CSR.scala 1565:26]
  wire [7:0] _T_60 = {reg_pmp_0_cfg_l,2'h0,reg_pmp_0_cfg_a,reg_pmp_0_cfg_x,reg_pmp_0_cfg_w,reg_pmp_0_cfg_r}; // @[package.scala 36:38]
  wire [7:0] _T_62 = {reg_pmp_2_cfg_l,2'h0,reg_pmp_2_cfg_a,reg_pmp_2_cfg_x,reg_pmp_2_cfg_w,reg_pmp_2_cfg_r}; // @[package.scala 36:38]
  wire [15:0] lo_11 = {reg_pmp_1_cfg_l,2'h0,reg_pmp_1_cfg_a,reg_pmp_1_cfg_x,reg_pmp_1_cfg_w,reg_pmp_1_cfg_r,_T_60}; // @[Cat.scala 31:58]
  wire [31:0] _T_64 = {reg_pmp_3_cfg_l,2'h0,reg_pmp_3_cfg_a,reg_pmp_3_cfg_x,reg_pmp_3_cfg_w,reg_pmp_3_cfg_r,_T_62,lo_11}
    ; // @[Cat.scala 31:58]
  wire [7:0] _T_65 = {reg_pmp_4_cfg_l,2'h0,reg_pmp_4_cfg_a,reg_pmp_4_cfg_x,reg_pmp_4_cfg_w,reg_pmp_4_cfg_r}; // @[package.scala 36:38]
  wire [7:0] _T_67 = {reg_pmp_6_cfg_l,2'h0,reg_pmp_6_cfg_a,reg_pmp_6_cfg_x,reg_pmp_6_cfg_w,reg_pmp_6_cfg_r}; // @[package.scala 36:38]
  wire [15:0] lo_16 = {reg_pmp_5_cfg_l,2'h0,reg_pmp_5_cfg_a,reg_pmp_5_cfg_x,reg_pmp_5_cfg_w,reg_pmp_5_cfg_r,_T_65}; // @[Cat.scala 31:58]
  wire [31:0] _T_69 = {reg_pmp_7_cfg_l,2'h0,reg_pmp_7_cfg_a,reg_pmp_7_cfg_x,reg_pmp_7_cfg_w,reg_pmp_7_cfg_r,_T_67,lo_16}
    ; // @[Cat.scala 31:58]
  reg [31:0] reg_custom_0; // @[CSR.scala 751:43]
  wire [12:0] addr = {io_status_v,io_rw_addr}; // @[Cat.scala 31:58]
  wire [11:0] decoded_decoded_plaInput = addr[11:0]; // @[decoder.scala 38:16 pla.scala 77:22]
  wire [11:0] decoded_decoded_invInputs = ~decoded_decoded_plaInput; // @[pla.scala 78:21]
  wire  decoded_decoded_andMatrixInput_0 = decoded_decoded_invInputs[0]; // @[pla.scala 91:29]
  wire  decoded_decoded_andMatrixInput_1 = decoded_decoded_invInputs[1]; // @[pla.scala 91:29]
  wire  decoded_decoded_andMatrixInput_2 = decoded_decoded_invInputs[2]; // @[pla.scala 91:29]
  wire  decoded_decoded_andMatrixInput_3 = decoded_decoded_invInputs[3]; // @[pla.scala 91:29]
  wire  decoded_decoded_andMatrixInput_4 = decoded_decoded_invInputs[4]; // @[pla.scala 91:29]
  wire  decoded_decoded_andMatrixInput_5 = decoded_decoded_invInputs[5]; // @[pla.scala 91:29]
  wire  decoded_decoded_andMatrixInput_6 = decoded_decoded_invInputs[6]; // @[pla.scala 91:29]
  wire  decoded_decoded_andMatrixInput_7 = decoded_decoded_invInputs[7]; // @[pla.scala 91:29]
  wire  decoded_decoded_andMatrixInput_8 = decoded_decoded_plaInput[8]; // @[pla.scala 90:45]
  wire  decoded_decoded_andMatrixInput_9 = decoded_decoded_plaInput[9]; // @[pla.scala 90:45]
  wire  decoded_decoded_andMatrixInput_10 = decoded_decoded_invInputs[10]; // @[pla.scala 91:29]
  wire  decoded_decoded_andMatrixInput_11 = decoded_decoded_invInputs[11]; // @[pla.scala 91:29]
  wire [5:0] decoded_decoded_lo = {decoded_decoded_andMatrixInput_6,decoded_decoded_andMatrixInput_7,
    decoded_decoded_andMatrixInput_8,decoded_decoded_andMatrixInput_9,decoded_decoded_andMatrixInput_10,
    decoded_decoded_andMatrixInput_11}; // @[Cat.scala 31:58]
  wire [11:0] _decoded_decoded_T = {decoded_decoded_andMatrixInput_0,decoded_decoded_andMatrixInput_1,
    decoded_decoded_andMatrixInput_2,decoded_decoded_andMatrixInput_3,decoded_decoded_andMatrixInput_4,
    decoded_decoded_andMatrixInput_5,decoded_decoded_lo}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_1 = &_decoded_decoded_T; // @[pla.scala 98:74]
  wire  decoded_decoded_andMatrixInput_0_1 = decoded_decoded_plaInput[0]; // @[pla.scala 90:45]
  wire [11:0] _decoded_decoded_T_2 = {decoded_decoded_andMatrixInput_0_1,decoded_decoded_andMatrixInput_1,
    decoded_decoded_andMatrixInput_2,decoded_decoded_andMatrixInput_3,decoded_decoded_andMatrixInput_4,
    decoded_decoded_andMatrixInput_5,decoded_decoded_lo}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_3 = &_decoded_decoded_T_2; // @[pla.scala 98:74]
  wire  decoded_decoded_andMatrixInput_2_2 = decoded_decoded_plaInput[2]; // @[pla.scala 90:45]
  wire [11:0] _decoded_decoded_T_4 = {decoded_decoded_andMatrixInput_0,decoded_decoded_andMatrixInput_1,
    decoded_decoded_andMatrixInput_2_2,decoded_decoded_andMatrixInput_3,decoded_decoded_andMatrixInput_4,
    decoded_decoded_andMatrixInput_5,decoded_decoded_lo}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_5 = &_decoded_decoded_T_4; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_6 = {decoded_decoded_andMatrixInput_0_1,decoded_decoded_andMatrixInput_1,
    decoded_decoded_andMatrixInput_2_2,decoded_decoded_andMatrixInput_3,decoded_decoded_andMatrixInput_4,
    decoded_decoded_andMatrixInput_5,decoded_decoded_lo}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_7 = &_decoded_decoded_T_6; // @[pla.scala 98:74]
  wire  decoded_decoded_andMatrixInput_4_4 = decoded_decoded_plaInput[5]; // @[pla.scala 90:45]
  wire [4:0] decoded_decoded_lo_4 = {decoded_decoded_andMatrixInput_7,decoded_decoded_andMatrixInput_8,
    decoded_decoded_andMatrixInput_9,decoded_decoded_andMatrixInput_10,decoded_decoded_andMatrixInput_11}; // @[Cat.scala 31:58]
  wire [10:0] _decoded_decoded_T_8 = {decoded_decoded_andMatrixInput_1,decoded_decoded_andMatrixInput_2,
    decoded_decoded_andMatrixInput_3,decoded_decoded_andMatrixInput_4,decoded_decoded_andMatrixInput_4_4,
    decoded_decoded_andMatrixInput_6,decoded_decoded_lo_4}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_9 = &_decoded_decoded_T_8; // @[pla.scala 98:74]
  wire  decoded_decoded_andMatrixInput_0_5 = decoded_decoded_plaInput[1]; // @[pla.scala 90:45]
  wire [10:0] _decoded_decoded_T_10 = {decoded_decoded_andMatrixInput_0_5,decoded_decoded_andMatrixInput_2,
    decoded_decoded_andMatrixInput_3,decoded_decoded_andMatrixInput_4,decoded_decoded_andMatrixInput_4_4,
    decoded_decoded_andMatrixInput_6,decoded_decoded_lo_4}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_11 = &_decoded_decoded_T_10; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_12 = {decoded_decoded_andMatrixInput_0,decoded_decoded_andMatrixInput_1,
    decoded_decoded_andMatrixInput_2_2,decoded_decoded_andMatrixInput_3,decoded_decoded_andMatrixInput_4,
    decoded_decoded_andMatrixInput_4_4,decoded_decoded_lo}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_13 = &_decoded_decoded_T_12; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_14 = {decoded_decoded_andMatrixInput_0_1,decoded_decoded_andMatrixInput_1,
    decoded_decoded_andMatrixInput_2_2,decoded_decoded_andMatrixInput_3,decoded_decoded_andMatrixInput_4,
    decoded_decoded_andMatrixInput_4_4,decoded_decoded_lo}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_15 = &_decoded_decoded_T_14; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_16 = {decoded_decoded_andMatrixInput_0,decoded_decoded_andMatrixInput_0_5,
    decoded_decoded_andMatrixInput_2_2,decoded_decoded_andMatrixInput_3,decoded_decoded_andMatrixInput_4,
    decoded_decoded_andMatrixInput_4_4,decoded_decoded_lo}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_17 = &_decoded_decoded_T_16; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_18 = {decoded_decoded_andMatrixInput_0_1,decoded_decoded_andMatrixInput_0_5,
    decoded_decoded_andMatrixInput_2_2,decoded_decoded_andMatrixInput_3,decoded_decoded_andMatrixInput_4,
    decoded_decoded_andMatrixInput_4_4,decoded_decoded_lo}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_19 = &_decoded_decoded_T_18; // @[pla.scala 98:74]
  wire  decoded_decoded_andMatrixInput_3_10 = decoded_decoded_plaInput[3]; // @[pla.scala 90:45]
  wire [11:0] _decoded_decoded_T_20 = {decoded_decoded_andMatrixInput_0,decoded_decoded_andMatrixInput_1,
    decoded_decoded_andMatrixInput_2,decoded_decoded_andMatrixInput_3_10,decoded_decoded_andMatrixInput_4,
    decoded_decoded_andMatrixInput_4_4,decoded_decoded_lo}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_21 = &_decoded_decoded_T_20; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_22 = {decoded_decoded_andMatrixInput_0_1,decoded_decoded_andMatrixInput_1,
    decoded_decoded_andMatrixInput_2,decoded_decoded_andMatrixInput_3_10,decoded_decoded_andMatrixInput_4,
    decoded_decoded_andMatrixInput_4_4,decoded_decoded_lo}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_23 = &_decoded_decoded_T_22; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_24 = {decoded_decoded_andMatrixInput_0,decoded_decoded_andMatrixInput_0_5,
    decoded_decoded_andMatrixInput_2,decoded_decoded_andMatrixInput_3_10,decoded_decoded_andMatrixInput_4,
    decoded_decoded_andMatrixInput_4_4,decoded_decoded_lo}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_25 = &_decoded_decoded_T_24; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_26 = {decoded_decoded_andMatrixInput_0_1,decoded_decoded_andMatrixInput_0_5,
    decoded_decoded_andMatrixInput_2,decoded_decoded_andMatrixInput_3_10,decoded_decoded_andMatrixInput_4,
    decoded_decoded_andMatrixInput_4_4,decoded_decoded_lo}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_27 = &_decoded_decoded_T_26; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_28 = {decoded_decoded_andMatrixInput_0,decoded_decoded_andMatrixInput_1,
    decoded_decoded_andMatrixInput_2_2,decoded_decoded_andMatrixInput_3_10,decoded_decoded_andMatrixInput_4,
    decoded_decoded_andMatrixInput_4_4,decoded_decoded_lo}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_29 = &_decoded_decoded_T_28; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_30 = {decoded_decoded_andMatrixInput_0_1,decoded_decoded_andMatrixInput_1,
    decoded_decoded_andMatrixInput_2_2,decoded_decoded_andMatrixInput_3_10,decoded_decoded_andMatrixInput_4,
    decoded_decoded_andMatrixInput_4_4,decoded_decoded_lo}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_31 = &_decoded_decoded_T_30; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_32 = {decoded_decoded_andMatrixInput_0,decoded_decoded_andMatrixInput_0_5,
    decoded_decoded_andMatrixInput_2_2,decoded_decoded_andMatrixInput_3_10,decoded_decoded_andMatrixInput_4,
    decoded_decoded_andMatrixInput_4_4,decoded_decoded_lo}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_33 = &_decoded_decoded_T_32; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_34 = {decoded_decoded_andMatrixInput_0_1,decoded_decoded_andMatrixInput_0_5,
    decoded_decoded_andMatrixInput_2_2,decoded_decoded_andMatrixInput_3_10,decoded_decoded_andMatrixInput_4,
    decoded_decoded_andMatrixInput_4_4,decoded_decoded_lo}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_35 = &_decoded_decoded_T_34; // @[pla.scala 98:74]
  wire  decoded_decoded_andMatrixInput_4_18 = decoded_decoded_plaInput[4]; // @[pla.scala 90:45]
  wire [11:0] _decoded_decoded_T_36 = {decoded_decoded_andMatrixInput_0,decoded_decoded_andMatrixInput_1,
    decoded_decoded_andMatrixInput_2,decoded_decoded_andMatrixInput_3,decoded_decoded_andMatrixInput_4_18,
    decoded_decoded_andMatrixInput_4_4,decoded_decoded_lo}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_37 = &_decoded_decoded_T_36; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_38 = {decoded_decoded_andMatrixInput_0_1,decoded_decoded_andMatrixInput_1,
    decoded_decoded_andMatrixInput_2,decoded_decoded_andMatrixInput_3,decoded_decoded_andMatrixInput_4_18,
    decoded_decoded_andMatrixInput_4_4,decoded_decoded_lo}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_39 = &_decoded_decoded_T_38; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_40 = {decoded_decoded_andMatrixInput_0,decoded_decoded_andMatrixInput_0_5,
    decoded_decoded_andMatrixInput_2,decoded_decoded_andMatrixInput_3,decoded_decoded_andMatrixInput_4_18,
    decoded_decoded_andMatrixInput_4_4,decoded_decoded_lo}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_41 = &_decoded_decoded_T_40; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_42 = {decoded_decoded_andMatrixInput_0_1,decoded_decoded_andMatrixInput_0_5,
    decoded_decoded_andMatrixInput_2,decoded_decoded_andMatrixInput_3,decoded_decoded_andMatrixInput_4_18,
    decoded_decoded_andMatrixInput_4_4,decoded_decoded_lo}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_43 = &_decoded_decoded_T_42; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_44 = {decoded_decoded_andMatrixInput_0,decoded_decoded_andMatrixInput_1,
    decoded_decoded_andMatrixInput_2_2,decoded_decoded_andMatrixInput_3,decoded_decoded_andMatrixInput_4_18,
    decoded_decoded_andMatrixInput_4_4,decoded_decoded_lo}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_45 = &_decoded_decoded_T_44; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_46 = {decoded_decoded_andMatrixInput_0_1,decoded_decoded_andMatrixInput_1,
    decoded_decoded_andMatrixInput_2_2,decoded_decoded_andMatrixInput_3,decoded_decoded_andMatrixInput_4_18,
    decoded_decoded_andMatrixInput_4_4,decoded_decoded_lo}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_47 = &_decoded_decoded_T_46; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_48 = {decoded_decoded_andMatrixInput_0,decoded_decoded_andMatrixInput_0_5,
    decoded_decoded_andMatrixInput_2_2,decoded_decoded_andMatrixInput_3,decoded_decoded_andMatrixInput_4_18,
    decoded_decoded_andMatrixInput_4_4,decoded_decoded_lo}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_49 = &_decoded_decoded_T_48; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_50 = {decoded_decoded_andMatrixInput_0_1,decoded_decoded_andMatrixInput_0_5,
    decoded_decoded_andMatrixInput_2_2,decoded_decoded_andMatrixInput_3,decoded_decoded_andMatrixInput_4_18,
    decoded_decoded_andMatrixInput_4_4,decoded_decoded_lo}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_51 = &_decoded_decoded_T_50; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_52 = {decoded_decoded_andMatrixInput_0,decoded_decoded_andMatrixInput_1,
    decoded_decoded_andMatrixInput_2,decoded_decoded_andMatrixInput_3_10,decoded_decoded_andMatrixInput_4_18,
    decoded_decoded_andMatrixInput_4_4,decoded_decoded_lo}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_53 = &_decoded_decoded_T_52; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_54 = {decoded_decoded_andMatrixInput_0_1,decoded_decoded_andMatrixInput_1,
    decoded_decoded_andMatrixInput_2,decoded_decoded_andMatrixInput_3_10,decoded_decoded_andMatrixInput_4_18,
    decoded_decoded_andMatrixInput_4_4,decoded_decoded_lo}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_55 = &_decoded_decoded_T_54; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_56 = {decoded_decoded_andMatrixInput_0,decoded_decoded_andMatrixInput_0_5,
    decoded_decoded_andMatrixInput_2,decoded_decoded_andMatrixInput_3_10,decoded_decoded_andMatrixInput_4_18,
    decoded_decoded_andMatrixInput_4_4,decoded_decoded_lo}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_57 = &_decoded_decoded_T_56; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_58 = {decoded_decoded_andMatrixInput_0_1,decoded_decoded_andMatrixInput_0_5,
    decoded_decoded_andMatrixInput_2,decoded_decoded_andMatrixInput_3_10,decoded_decoded_andMatrixInput_4_18,
    decoded_decoded_andMatrixInput_4_4,decoded_decoded_lo}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_59 = &_decoded_decoded_T_58; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_60 = {decoded_decoded_andMatrixInput_0,decoded_decoded_andMatrixInput_1,
    decoded_decoded_andMatrixInput_2_2,decoded_decoded_andMatrixInput_3_10,decoded_decoded_andMatrixInput_4_18,
    decoded_decoded_andMatrixInput_4_4,decoded_decoded_lo}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_61 = &_decoded_decoded_T_60; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_62 = {decoded_decoded_andMatrixInput_0_1,decoded_decoded_andMatrixInput_1,
    decoded_decoded_andMatrixInput_2_2,decoded_decoded_andMatrixInput_3_10,decoded_decoded_andMatrixInput_4_18,
    decoded_decoded_andMatrixInput_4_4,decoded_decoded_lo}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_63 = &_decoded_decoded_T_62; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_64 = {decoded_decoded_andMatrixInput_0,decoded_decoded_andMatrixInput_0_5,
    decoded_decoded_andMatrixInput_2_2,decoded_decoded_andMatrixInput_3_10,decoded_decoded_andMatrixInput_4_18,
    decoded_decoded_andMatrixInput_4_4,decoded_decoded_lo}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_65 = &_decoded_decoded_T_64; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_66 = {decoded_decoded_andMatrixInput_0_1,decoded_decoded_andMatrixInput_0_5,
    decoded_decoded_andMatrixInput_2_2,decoded_decoded_andMatrixInput_3_10,decoded_decoded_andMatrixInput_4_18,
    decoded_decoded_andMatrixInput_4_4,decoded_decoded_lo}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_67 = &_decoded_decoded_T_66; // @[pla.scala 98:74]
  wire  decoded_decoded_andMatrixInput_6_34 = decoded_decoded_plaInput[6]; // @[pla.scala 90:45]
  wire [5:0] decoded_decoded_lo_34 = {decoded_decoded_andMatrixInput_6_34,decoded_decoded_andMatrixInput_7,
    decoded_decoded_andMatrixInput_8,decoded_decoded_andMatrixInput_9,decoded_decoded_andMatrixInput_10,
    decoded_decoded_andMatrixInput_11}; // @[Cat.scala 31:58]
  wire [11:0] _decoded_decoded_T_68 = {decoded_decoded_andMatrixInput_0,decoded_decoded_andMatrixInput_1,
    decoded_decoded_andMatrixInput_2,decoded_decoded_andMatrixInput_3,decoded_decoded_andMatrixInput_4,
    decoded_decoded_andMatrixInput_5,decoded_decoded_lo_34}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_69 = &_decoded_decoded_T_68; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_70 = {decoded_decoded_andMatrixInput_0_1,decoded_decoded_andMatrixInput_1,
    decoded_decoded_andMatrixInput_2,decoded_decoded_andMatrixInput_3,decoded_decoded_andMatrixInput_4,
    decoded_decoded_andMatrixInput_5,decoded_decoded_lo_34}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_71 = &_decoded_decoded_T_70; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_72 = {decoded_decoded_andMatrixInput_0,decoded_decoded_andMatrixInput_0_5,
    decoded_decoded_andMatrixInput_2,decoded_decoded_andMatrixInput_3,decoded_decoded_andMatrixInput_4,
    decoded_decoded_andMatrixInput_5,decoded_decoded_lo_34}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_73 = &_decoded_decoded_T_72; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_74 = {decoded_decoded_andMatrixInput_0_1,decoded_decoded_andMatrixInput_0_5,
    decoded_decoded_andMatrixInput_2,decoded_decoded_andMatrixInput_3,decoded_decoded_andMatrixInput_4,
    decoded_decoded_andMatrixInput_5,decoded_decoded_lo_34}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_75 = &_decoded_decoded_T_74; // @[pla.scala 98:74]
  wire [9:0] _decoded_decoded_T_76 = {decoded_decoded_andMatrixInput_2_2,decoded_decoded_andMatrixInput_3,
    decoded_decoded_andMatrixInput_4,decoded_decoded_andMatrixInput_5,decoded_decoded_andMatrixInput_6_34,
    decoded_decoded_andMatrixInput_7,decoded_decoded_andMatrixInput_8,decoded_decoded_andMatrixInput_9,
    decoded_decoded_andMatrixInput_10,decoded_decoded_andMatrixInput_11}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_77 = &_decoded_decoded_T_76; // @[pla.scala 98:74]
  wire  decoded_decoded_andMatrixInput_7_39 = decoded_decoded_plaInput[7]; // @[pla.scala 90:45]
  wire [5:0] decoded_decoded_lo_39 = {decoded_decoded_andMatrixInput_6,decoded_decoded_andMatrixInput_7_39,
    decoded_decoded_andMatrixInput_8,decoded_decoded_andMatrixInput_9,decoded_decoded_andMatrixInput_10,
    decoded_decoded_andMatrixInput_11}; // @[Cat.scala 31:58]
  wire [11:0] _decoded_decoded_T_78 = {decoded_decoded_andMatrixInput_0,decoded_decoded_andMatrixInput_1,
    decoded_decoded_andMatrixInput_2,decoded_decoded_andMatrixInput_3,decoded_decoded_andMatrixInput_4,
    decoded_decoded_andMatrixInput_4_4,decoded_decoded_lo_39}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_79 = &_decoded_decoded_T_78; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_80 = {decoded_decoded_andMatrixInput_0_1,decoded_decoded_andMatrixInput_1,
    decoded_decoded_andMatrixInput_2,decoded_decoded_andMatrixInput_3,decoded_decoded_andMatrixInput_4,
    decoded_decoded_andMatrixInput_4_4,decoded_decoded_lo_39}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_81 = &_decoded_decoded_T_80; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_82 = {decoded_decoded_andMatrixInput_0,decoded_decoded_andMatrixInput_0_5,
    decoded_decoded_andMatrixInput_2,decoded_decoded_andMatrixInput_3,decoded_decoded_andMatrixInput_4,
    decoded_decoded_andMatrixInput_4_4,decoded_decoded_lo_39}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_83 = &_decoded_decoded_T_82; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_84 = {decoded_decoded_andMatrixInput_0_1,decoded_decoded_andMatrixInput_0_5,
    decoded_decoded_andMatrixInput_2,decoded_decoded_andMatrixInput_3,decoded_decoded_andMatrixInput_4,
    decoded_decoded_andMatrixInput_4_4,decoded_decoded_lo_39}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_85 = &_decoded_decoded_T_84; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_86 = {decoded_decoded_andMatrixInput_0,decoded_decoded_andMatrixInput_1,
    decoded_decoded_andMatrixInput_2,decoded_decoded_andMatrixInput_3,decoded_decoded_andMatrixInput_4_18,
    decoded_decoded_andMatrixInput_4_4,decoded_decoded_lo_39}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_87 = &_decoded_decoded_T_86; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_88 = {decoded_decoded_andMatrixInput_0_1,decoded_decoded_andMatrixInput_1,
    decoded_decoded_andMatrixInput_2,decoded_decoded_andMatrixInput_3,decoded_decoded_andMatrixInput_4_18,
    decoded_decoded_andMatrixInput_4_4,decoded_decoded_lo_39}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_89 = &_decoded_decoded_T_88; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_90 = {decoded_decoded_andMatrixInput_0,decoded_decoded_andMatrixInput_0_5,
    decoded_decoded_andMatrixInput_2,decoded_decoded_andMatrixInput_3,decoded_decoded_andMatrixInput_4_18,
    decoded_decoded_andMatrixInput_4_4,decoded_decoded_lo_39}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_91 = &_decoded_decoded_T_90; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_92 = {decoded_decoded_andMatrixInput_0_1,decoded_decoded_andMatrixInput_0_5,
    decoded_decoded_andMatrixInput_2,decoded_decoded_andMatrixInput_3,decoded_decoded_andMatrixInput_4_18,
    decoded_decoded_andMatrixInput_4_4,decoded_decoded_lo_39}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_93 = &_decoded_decoded_T_92; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_94 = {decoded_decoded_andMatrixInput_0,decoded_decoded_andMatrixInput_1,
    decoded_decoded_andMatrixInput_2_2,decoded_decoded_andMatrixInput_3,decoded_decoded_andMatrixInput_4_18,
    decoded_decoded_andMatrixInput_4_4,decoded_decoded_lo_39}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_95 = &_decoded_decoded_T_94; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_96 = {decoded_decoded_andMatrixInput_0_1,decoded_decoded_andMatrixInput_1,
    decoded_decoded_andMatrixInput_2_2,decoded_decoded_andMatrixInput_3,decoded_decoded_andMatrixInput_4_18,
    decoded_decoded_andMatrixInput_4_4,decoded_decoded_lo_39}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_97 = &_decoded_decoded_T_96; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_98 = {decoded_decoded_andMatrixInput_0,decoded_decoded_andMatrixInput_0_5,
    decoded_decoded_andMatrixInput_2_2,decoded_decoded_andMatrixInput_3,decoded_decoded_andMatrixInput_4_18,
    decoded_decoded_andMatrixInput_4_4,decoded_decoded_lo_39}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_99 = &_decoded_decoded_T_98; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_100 = {decoded_decoded_andMatrixInput_0_1,decoded_decoded_andMatrixInput_0_5,
    decoded_decoded_andMatrixInput_2_2,decoded_decoded_andMatrixInput_3,decoded_decoded_andMatrixInput_4_18,
    decoded_decoded_andMatrixInput_4_4,decoded_decoded_lo_39}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_101 = &_decoded_decoded_T_100; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_102 = {decoded_decoded_andMatrixInput_0,decoded_decoded_andMatrixInput_1,
    decoded_decoded_andMatrixInput_2,decoded_decoded_andMatrixInput_3_10,decoded_decoded_andMatrixInput_4_18,
    decoded_decoded_andMatrixInput_4_4,decoded_decoded_lo_39}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_103 = &_decoded_decoded_T_102; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_104 = {decoded_decoded_andMatrixInput_0_1,decoded_decoded_andMatrixInput_1,
    decoded_decoded_andMatrixInput_2,decoded_decoded_andMatrixInput_3_10,decoded_decoded_andMatrixInput_4_18,
    decoded_decoded_andMatrixInput_4_4,decoded_decoded_lo_39}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_105 = &_decoded_decoded_T_104; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_106 = {decoded_decoded_andMatrixInput_0,decoded_decoded_andMatrixInput_0_5,
    decoded_decoded_andMatrixInput_2,decoded_decoded_andMatrixInput_3_10,decoded_decoded_andMatrixInput_4_18,
    decoded_decoded_andMatrixInput_4_4,decoded_decoded_lo_39}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_107 = &_decoded_decoded_T_106; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_108 = {decoded_decoded_andMatrixInput_0_1,decoded_decoded_andMatrixInput_0_5,
    decoded_decoded_andMatrixInput_2,decoded_decoded_andMatrixInput_3_10,decoded_decoded_andMatrixInput_4_18,
    decoded_decoded_andMatrixInput_4_4,decoded_decoded_lo_39}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_109 = &_decoded_decoded_T_108; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_110 = {decoded_decoded_andMatrixInput_0,decoded_decoded_andMatrixInput_1,
    decoded_decoded_andMatrixInput_2_2,decoded_decoded_andMatrixInput_3_10,decoded_decoded_andMatrixInput_4_18,
    decoded_decoded_andMatrixInput_4_4,decoded_decoded_lo_39}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_111 = &_decoded_decoded_T_110; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_112 = {decoded_decoded_andMatrixInput_0_1,decoded_decoded_andMatrixInput_1,
    decoded_decoded_andMatrixInput_2_2,decoded_decoded_andMatrixInput_3_10,decoded_decoded_andMatrixInput_4_18,
    decoded_decoded_andMatrixInput_4_4,decoded_decoded_lo_39}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_113 = &_decoded_decoded_T_112; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_114 = {decoded_decoded_andMatrixInput_0,decoded_decoded_andMatrixInput_0_5,
    decoded_decoded_andMatrixInput_2_2,decoded_decoded_andMatrixInput_3_10,decoded_decoded_andMatrixInput_4_18,
    decoded_decoded_andMatrixInput_4_4,decoded_decoded_lo_39}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_115 = &_decoded_decoded_T_114; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_116 = {decoded_decoded_andMatrixInput_0_1,decoded_decoded_andMatrixInput_0_5,
    decoded_decoded_andMatrixInput_2_2,decoded_decoded_andMatrixInput_3_10,decoded_decoded_andMatrixInput_4_18,
    decoded_decoded_andMatrixInput_4_4,decoded_decoded_lo_39}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_117 = &_decoded_decoded_T_116; // @[pla.scala 98:74]
  wire  decoded_decoded_andMatrixInput_10_58 = decoded_decoded_plaInput[10]; // @[pla.scala 90:45]
  wire [5:0] decoded_decoded_lo_59 = {decoded_decoded_andMatrixInput_6,decoded_decoded_andMatrixInput_7_39,
    decoded_decoded_andMatrixInput_8,decoded_decoded_andMatrixInput_9,decoded_decoded_andMatrixInput_10_58,
    decoded_decoded_andMatrixInput_11}; // @[Cat.scala 31:58]
  wire [11:0] _decoded_decoded_T_118 = {decoded_decoded_andMatrixInput_0,decoded_decoded_andMatrixInput_1,
    decoded_decoded_andMatrixInput_2,decoded_decoded_andMatrixInput_3,decoded_decoded_andMatrixInput_4,
    decoded_decoded_andMatrixInput_4_4,decoded_decoded_lo_59}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_119 = &_decoded_decoded_T_118; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_120 = {decoded_decoded_andMatrixInput_0_1,decoded_decoded_andMatrixInput_1,
    decoded_decoded_andMatrixInput_2,decoded_decoded_andMatrixInput_3,decoded_decoded_andMatrixInput_4,
    decoded_decoded_andMatrixInput_4_4,decoded_decoded_lo_59}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_121 = &_decoded_decoded_T_120; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_122 = {decoded_decoded_andMatrixInput_0,decoded_decoded_andMatrixInput_0_5,
    decoded_decoded_andMatrixInput_2,decoded_decoded_andMatrixInput_3,decoded_decoded_andMatrixInput_4,
    decoded_decoded_andMatrixInput_4_4,decoded_decoded_lo_59}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_123 = &_decoded_decoded_T_122; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_124 = {decoded_decoded_andMatrixInput_0_1,decoded_decoded_andMatrixInput_0_5,
    decoded_decoded_andMatrixInput_2,decoded_decoded_andMatrixInput_3,decoded_decoded_andMatrixInput_4,
    decoded_decoded_andMatrixInput_4_4,decoded_decoded_lo_59}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_125 = &_decoded_decoded_T_124; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_126 = {decoded_decoded_andMatrixInput_0,decoded_decoded_andMatrixInput_1,
    decoded_decoded_andMatrixInput_2,decoded_decoded_andMatrixInput_3,decoded_decoded_andMatrixInput_4_18,
    decoded_decoded_andMatrixInput_4_4,decoded_decoded_lo_59}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_127 = &_decoded_decoded_T_126; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_128 = {decoded_decoded_andMatrixInput_0_1,decoded_decoded_andMatrixInput_1,
    decoded_decoded_andMatrixInput_2,decoded_decoded_andMatrixInput_3,decoded_decoded_andMatrixInput_4_18,
    decoded_decoded_andMatrixInput_4_4,decoded_decoded_lo_59}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_129 = &_decoded_decoded_T_128; // @[pla.scala 98:74]
  wire [4:0] decoded_decoded_lo_65 = {decoded_decoded_andMatrixInput_7_39,decoded_decoded_andMatrixInput_8,
    decoded_decoded_andMatrixInput_9,decoded_decoded_andMatrixInput_10_58,decoded_decoded_andMatrixInput_11}; // @[Cat.scala 31:58]
  wire [10:0] _decoded_decoded_T_130 = {decoded_decoded_andMatrixInput_0_5,decoded_decoded_andMatrixInput_2,
    decoded_decoded_andMatrixInput_3,decoded_decoded_andMatrixInput_4_18,decoded_decoded_andMatrixInput_4_4,
    decoded_decoded_andMatrixInput_6,decoded_decoded_lo_65}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_131 = &_decoded_decoded_T_130; // @[pla.scala 98:74]
  wire [5:0] _decoded_decoded_T_132 = {decoded_decoded_andMatrixInput_6_34,decoded_decoded_andMatrixInput_7_39,
    decoded_decoded_andMatrixInput_8,decoded_decoded_andMatrixInput_9,decoded_decoded_andMatrixInput_10_58,
    decoded_decoded_andMatrixInput_11}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_133 = &_decoded_decoded_T_132; // @[pla.scala 98:74]
  wire  decoded_decoded_andMatrixInput_10_65 = decoded_decoded_plaInput[11]; // @[pla.scala 90:45]
  wire [4:0] decoded_decoded_lo_67 = {decoded_decoded_andMatrixInput_7,decoded_decoded_andMatrixInput_8,
    decoded_decoded_andMatrixInput_9,decoded_decoded_andMatrixInput_10,decoded_decoded_andMatrixInput_10_65}; // @[Cat.scala 31:58]
  wire [10:0] _decoded_decoded_T_134 = {decoded_decoded_andMatrixInput_1,decoded_decoded_andMatrixInput_2,
    decoded_decoded_andMatrixInput_3,decoded_decoded_andMatrixInput_4,decoded_decoded_andMatrixInput_5,
    decoded_decoded_andMatrixInput_6,decoded_decoded_lo_67}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_135 = &_decoded_decoded_T_134; // @[pla.scala 98:74]
  wire [5:0] decoded_decoded_lo_68 = {decoded_decoded_andMatrixInput_6,decoded_decoded_andMatrixInput_7,
    decoded_decoded_andMatrixInput_8,decoded_decoded_andMatrixInput_9,decoded_decoded_andMatrixInput_10,
    decoded_decoded_andMatrixInput_10_65}; // @[Cat.scala 31:58]
  wire [11:0] _decoded_decoded_T_136 = {decoded_decoded_andMatrixInput_0,decoded_decoded_andMatrixInput_0_5,
    decoded_decoded_andMatrixInput_2,decoded_decoded_andMatrixInput_3,decoded_decoded_andMatrixInput_4,
    decoded_decoded_andMatrixInput_5,decoded_decoded_lo_68}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_137 = &_decoded_decoded_T_136; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_138 = {decoded_decoded_andMatrixInput_0_1,decoded_decoded_andMatrixInput_0_5,
    decoded_decoded_andMatrixInput_2,decoded_decoded_andMatrixInput_3,decoded_decoded_andMatrixInput_4,
    decoded_decoded_andMatrixInput_5,decoded_decoded_lo_68}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_139 = &_decoded_decoded_T_138; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_140 = {decoded_decoded_andMatrixInput_0,decoded_decoded_andMatrixInput_1,
    decoded_decoded_andMatrixInput_2_2,decoded_decoded_andMatrixInput_3,decoded_decoded_andMatrixInput_4,
    decoded_decoded_andMatrixInput_5,decoded_decoded_lo_68}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_141 = &_decoded_decoded_T_140; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_142 = {decoded_decoded_andMatrixInput_0_1,decoded_decoded_andMatrixInput_1,
    decoded_decoded_andMatrixInput_2_2,decoded_decoded_andMatrixInput_3,decoded_decoded_andMatrixInput_4,
    decoded_decoded_andMatrixInput_5,decoded_decoded_lo_68}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_143 = &_decoded_decoded_T_142; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_144 = {decoded_decoded_andMatrixInput_0,decoded_decoded_andMatrixInput_0_5,
    decoded_decoded_andMatrixInput_2_2,decoded_decoded_andMatrixInput_3,decoded_decoded_andMatrixInput_4,
    decoded_decoded_andMatrixInput_5,decoded_decoded_lo_68}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_145 = &_decoded_decoded_T_144; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_146 = {decoded_decoded_andMatrixInput_0_1,decoded_decoded_andMatrixInput_0_5,
    decoded_decoded_andMatrixInput_2_2,decoded_decoded_andMatrixInput_3,decoded_decoded_andMatrixInput_4,
    decoded_decoded_andMatrixInput_5,decoded_decoded_lo_68}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_147 = &_decoded_decoded_T_146; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_148 = {decoded_decoded_andMatrixInput_0,decoded_decoded_andMatrixInput_1,
    decoded_decoded_andMatrixInput_2,decoded_decoded_andMatrixInput_3_10,decoded_decoded_andMatrixInput_4,
    decoded_decoded_andMatrixInput_5,decoded_decoded_lo_68}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_149 = &_decoded_decoded_T_148; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_150 = {decoded_decoded_andMatrixInput_0_1,decoded_decoded_andMatrixInput_1,
    decoded_decoded_andMatrixInput_2,decoded_decoded_andMatrixInput_3_10,decoded_decoded_andMatrixInput_4,
    decoded_decoded_andMatrixInput_5,decoded_decoded_lo_68}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_151 = &_decoded_decoded_T_150; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_152 = {decoded_decoded_andMatrixInput_0,decoded_decoded_andMatrixInput_0_5,
    decoded_decoded_andMatrixInput_2,decoded_decoded_andMatrixInput_3_10,decoded_decoded_andMatrixInput_4,
    decoded_decoded_andMatrixInput_5,decoded_decoded_lo_68}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_153 = &_decoded_decoded_T_152; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_154 = {decoded_decoded_andMatrixInput_0_1,decoded_decoded_andMatrixInput_0_5,
    decoded_decoded_andMatrixInput_2,decoded_decoded_andMatrixInput_3_10,decoded_decoded_andMatrixInput_4,
    decoded_decoded_andMatrixInput_5,decoded_decoded_lo_68}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_155 = &_decoded_decoded_T_154; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_156 = {decoded_decoded_andMatrixInput_0,decoded_decoded_andMatrixInput_1,
    decoded_decoded_andMatrixInput_2_2,decoded_decoded_andMatrixInput_3_10,decoded_decoded_andMatrixInput_4,
    decoded_decoded_andMatrixInput_5,decoded_decoded_lo_68}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_157 = &_decoded_decoded_T_156; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_158 = {decoded_decoded_andMatrixInput_0_1,decoded_decoded_andMatrixInput_1,
    decoded_decoded_andMatrixInput_2_2,decoded_decoded_andMatrixInput_3_10,decoded_decoded_andMatrixInput_4,
    decoded_decoded_andMatrixInput_5,decoded_decoded_lo_68}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_159 = &_decoded_decoded_T_158; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_160 = {decoded_decoded_andMatrixInput_0,decoded_decoded_andMatrixInput_0_5,
    decoded_decoded_andMatrixInput_2_2,decoded_decoded_andMatrixInput_3_10,decoded_decoded_andMatrixInput_4,
    decoded_decoded_andMatrixInput_5,decoded_decoded_lo_68}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_161 = &_decoded_decoded_T_160; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_162 = {decoded_decoded_andMatrixInput_0_1,decoded_decoded_andMatrixInput_0_5,
    decoded_decoded_andMatrixInput_2_2,decoded_decoded_andMatrixInput_3_10,decoded_decoded_andMatrixInput_4,
    decoded_decoded_andMatrixInput_5,decoded_decoded_lo_68}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_163 = &_decoded_decoded_T_162; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_164 = {decoded_decoded_andMatrixInput_0,decoded_decoded_andMatrixInput_1,
    decoded_decoded_andMatrixInput_2,decoded_decoded_andMatrixInput_3,decoded_decoded_andMatrixInput_4_18,
    decoded_decoded_andMatrixInput_5,decoded_decoded_lo_68}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_165 = &_decoded_decoded_T_164; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_166 = {decoded_decoded_andMatrixInput_0_1,decoded_decoded_andMatrixInput_1,
    decoded_decoded_andMatrixInput_2,decoded_decoded_andMatrixInput_3,decoded_decoded_andMatrixInput_4_18,
    decoded_decoded_andMatrixInput_5,decoded_decoded_lo_68}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_167 = &_decoded_decoded_T_166; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_168 = {decoded_decoded_andMatrixInput_0,decoded_decoded_andMatrixInput_0_5,
    decoded_decoded_andMatrixInput_2,decoded_decoded_andMatrixInput_3,decoded_decoded_andMatrixInput_4_18,
    decoded_decoded_andMatrixInput_5,decoded_decoded_lo_68}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_169 = &_decoded_decoded_T_168; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_170 = {decoded_decoded_andMatrixInput_0_1,decoded_decoded_andMatrixInput_0_5,
    decoded_decoded_andMatrixInput_2,decoded_decoded_andMatrixInput_3,decoded_decoded_andMatrixInput_4_18,
    decoded_decoded_andMatrixInput_5,decoded_decoded_lo_68}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_171 = &_decoded_decoded_T_170; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_172 = {decoded_decoded_andMatrixInput_0,decoded_decoded_andMatrixInput_1,
    decoded_decoded_andMatrixInput_2_2,decoded_decoded_andMatrixInput_3,decoded_decoded_andMatrixInput_4_18,
    decoded_decoded_andMatrixInput_5,decoded_decoded_lo_68}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_173 = &_decoded_decoded_T_172; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_174 = {decoded_decoded_andMatrixInput_0_1,decoded_decoded_andMatrixInput_1,
    decoded_decoded_andMatrixInput_2_2,decoded_decoded_andMatrixInput_3,decoded_decoded_andMatrixInput_4_18,
    decoded_decoded_andMatrixInput_5,decoded_decoded_lo_68}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_175 = &_decoded_decoded_T_174; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_176 = {decoded_decoded_andMatrixInput_0,decoded_decoded_andMatrixInput_0_5,
    decoded_decoded_andMatrixInput_2_2,decoded_decoded_andMatrixInput_3,decoded_decoded_andMatrixInput_4_18,
    decoded_decoded_andMatrixInput_5,decoded_decoded_lo_68}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_177 = &_decoded_decoded_T_176; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_178 = {decoded_decoded_andMatrixInput_0_1,decoded_decoded_andMatrixInput_0_5,
    decoded_decoded_andMatrixInput_2_2,decoded_decoded_andMatrixInput_3,decoded_decoded_andMatrixInput_4_18,
    decoded_decoded_andMatrixInput_5,decoded_decoded_lo_68}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_179 = &_decoded_decoded_T_178; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_180 = {decoded_decoded_andMatrixInput_0,decoded_decoded_andMatrixInput_1,
    decoded_decoded_andMatrixInput_2,decoded_decoded_andMatrixInput_3_10,decoded_decoded_andMatrixInput_4_18,
    decoded_decoded_andMatrixInput_5,decoded_decoded_lo_68}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_181 = &_decoded_decoded_T_180; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_182 = {decoded_decoded_andMatrixInput_0_1,decoded_decoded_andMatrixInput_1,
    decoded_decoded_andMatrixInput_2,decoded_decoded_andMatrixInput_3_10,decoded_decoded_andMatrixInput_4_18,
    decoded_decoded_andMatrixInput_5,decoded_decoded_lo_68}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_183 = &_decoded_decoded_T_182; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_184 = {decoded_decoded_andMatrixInput_0,decoded_decoded_andMatrixInput_0_5,
    decoded_decoded_andMatrixInput_2,decoded_decoded_andMatrixInput_3_10,decoded_decoded_andMatrixInput_4_18,
    decoded_decoded_andMatrixInput_5,decoded_decoded_lo_68}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_185 = &_decoded_decoded_T_184; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_186 = {decoded_decoded_andMatrixInput_0_1,decoded_decoded_andMatrixInput_0_5,
    decoded_decoded_andMatrixInput_2,decoded_decoded_andMatrixInput_3_10,decoded_decoded_andMatrixInput_4_18,
    decoded_decoded_andMatrixInput_5,decoded_decoded_lo_68}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_187 = &_decoded_decoded_T_186; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_188 = {decoded_decoded_andMatrixInput_0,decoded_decoded_andMatrixInput_1,
    decoded_decoded_andMatrixInput_2_2,decoded_decoded_andMatrixInput_3_10,decoded_decoded_andMatrixInput_4_18,
    decoded_decoded_andMatrixInput_5,decoded_decoded_lo_68}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_189 = &_decoded_decoded_T_188; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_190 = {decoded_decoded_andMatrixInput_0_1,decoded_decoded_andMatrixInput_1,
    decoded_decoded_andMatrixInput_2_2,decoded_decoded_andMatrixInput_3_10,decoded_decoded_andMatrixInput_4_18,
    decoded_decoded_andMatrixInput_5,decoded_decoded_lo_68}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_191 = &_decoded_decoded_T_190; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_192 = {decoded_decoded_andMatrixInput_0,decoded_decoded_andMatrixInput_0_5,
    decoded_decoded_andMatrixInput_2_2,decoded_decoded_andMatrixInput_3_10,decoded_decoded_andMatrixInput_4_18,
    decoded_decoded_andMatrixInput_5,decoded_decoded_lo_68}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_193 = &_decoded_decoded_T_192; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_194 = {decoded_decoded_andMatrixInput_0_1,decoded_decoded_andMatrixInput_0_5,
    decoded_decoded_andMatrixInput_2_2,decoded_decoded_andMatrixInput_3_10,decoded_decoded_andMatrixInput_4_18,
    decoded_decoded_andMatrixInput_5,decoded_decoded_lo_68}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_195 = &_decoded_decoded_T_194; // @[pla.scala 98:74]
  wire [4:0] decoded_decoded_lo_98 = {decoded_decoded_andMatrixInput_7_39,decoded_decoded_andMatrixInput_8,
    decoded_decoded_andMatrixInput_9,decoded_decoded_andMatrixInput_10,decoded_decoded_andMatrixInput_10_65}; // @[Cat.scala 31:58]
  wire [10:0] _decoded_decoded_T_196 = {decoded_decoded_andMatrixInput_1,decoded_decoded_andMatrixInput_2,
    decoded_decoded_andMatrixInput_3,decoded_decoded_andMatrixInput_4,decoded_decoded_andMatrixInput_5,
    decoded_decoded_andMatrixInput_6,decoded_decoded_lo_98}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_197 = &_decoded_decoded_T_196; // @[pla.scala 98:74]
  wire [5:0] decoded_decoded_lo_99 = {decoded_decoded_andMatrixInput_6,decoded_decoded_andMatrixInput_7_39,
    decoded_decoded_andMatrixInput_8,decoded_decoded_andMatrixInput_9,decoded_decoded_andMatrixInput_10,
    decoded_decoded_andMatrixInput_10_65}; // @[Cat.scala 31:58]
  wire [11:0] _decoded_decoded_T_198 = {decoded_decoded_andMatrixInput_0,decoded_decoded_andMatrixInput_0_5,
    decoded_decoded_andMatrixInput_2,decoded_decoded_andMatrixInput_3,decoded_decoded_andMatrixInput_4,
    decoded_decoded_andMatrixInput_5,decoded_decoded_lo_99}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_199 = &_decoded_decoded_T_198; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_200 = {decoded_decoded_andMatrixInput_0_1,decoded_decoded_andMatrixInput_0_5,
    decoded_decoded_andMatrixInput_2,decoded_decoded_andMatrixInput_3,decoded_decoded_andMatrixInput_4,
    decoded_decoded_andMatrixInput_5,decoded_decoded_lo_99}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_201 = &_decoded_decoded_T_200; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_202 = {decoded_decoded_andMatrixInput_0,decoded_decoded_andMatrixInput_1,
    decoded_decoded_andMatrixInput_2_2,decoded_decoded_andMatrixInput_3,decoded_decoded_andMatrixInput_4,
    decoded_decoded_andMatrixInput_5,decoded_decoded_lo_99}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_203 = &_decoded_decoded_T_202; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_204 = {decoded_decoded_andMatrixInput_0_1,decoded_decoded_andMatrixInput_1,
    decoded_decoded_andMatrixInput_2_2,decoded_decoded_andMatrixInput_3,decoded_decoded_andMatrixInput_4,
    decoded_decoded_andMatrixInput_5,decoded_decoded_lo_99}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_205 = &_decoded_decoded_T_204; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_206 = {decoded_decoded_andMatrixInput_0,decoded_decoded_andMatrixInput_0_5,
    decoded_decoded_andMatrixInput_2_2,decoded_decoded_andMatrixInput_3,decoded_decoded_andMatrixInput_4,
    decoded_decoded_andMatrixInput_5,decoded_decoded_lo_99}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_207 = &_decoded_decoded_T_206; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_208 = {decoded_decoded_andMatrixInput_0_1,decoded_decoded_andMatrixInput_0_5,
    decoded_decoded_andMatrixInput_2_2,decoded_decoded_andMatrixInput_3,decoded_decoded_andMatrixInput_4,
    decoded_decoded_andMatrixInput_5,decoded_decoded_lo_99}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_209 = &_decoded_decoded_T_208; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_210 = {decoded_decoded_andMatrixInput_0,decoded_decoded_andMatrixInput_1,
    decoded_decoded_andMatrixInput_2,decoded_decoded_andMatrixInput_3_10,decoded_decoded_andMatrixInput_4,
    decoded_decoded_andMatrixInput_5,decoded_decoded_lo_99}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_211 = &_decoded_decoded_T_210; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_212 = {decoded_decoded_andMatrixInput_0_1,decoded_decoded_andMatrixInput_1,
    decoded_decoded_andMatrixInput_2,decoded_decoded_andMatrixInput_3_10,decoded_decoded_andMatrixInput_4,
    decoded_decoded_andMatrixInput_5,decoded_decoded_lo_99}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_213 = &_decoded_decoded_T_212; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_214 = {decoded_decoded_andMatrixInput_0,decoded_decoded_andMatrixInput_0_5,
    decoded_decoded_andMatrixInput_2,decoded_decoded_andMatrixInput_3_10,decoded_decoded_andMatrixInput_4,
    decoded_decoded_andMatrixInput_5,decoded_decoded_lo_99}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_215 = &_decoded_decoded_T_214; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_216 = {decoded_decoded_andMatrixInput_0_1,decoded_decoded_andMatrixInput_0_5,
    decoded_decoded_andMatrixInput_2,decoded_decoded_andMatrixInput_3_10,decoded_decoded_andMatrixInput_4,
    decoded_decoded_andMatrixInput_5,decoded_decoded_lo_99}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_217 = &_decoded_decoded_T_216; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_218 = {decoded_decoded_andMatrixInput_0,decoded_decoded_andMatrixInput_1,
    decoded_decoded_andMatrixInput_2_2,decoded_decoded_andMatrixInput_3_10,decoded_decoded_andMatrixInput_4,
    decoded_decoded_andMatrixInput_5,decoded_decoded_lo_99}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_219 = &_decoded_decoded_T_218; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_220 = {decoded_decoded_andMatrixInput_0_1,decoded_decoded_andMatrixInput_1,
    decoded_decoded_andMatrixInput_2_2,decoded_decoded_andMatrixInput_3_10,decoded_decoded_andMatrixInput_4,
    decoded_decoded_andMatrixInput_5,decoded_decoded_lo_99}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_221 = &_decoded_decoded_T_220; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_222 = {decoded_decoded_andMatrixInput_0,decoded_decoded_andMatrixInput_0_5,
    decoded_decoded_andMatrixInput_2_2,decoded_decoded_andMatrixInput_3_10,decoded_decoded_andMatrixInput_4,
    decoded_decoded_andMatrixInput_5,decoded_decoded_lo_99}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_223 = &_decoded_decoded_T_222; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_224 = {decoded_decoded_andMatrixInput_0_1,decoded_decoded_andMatrixInput_0_5,
    decoded_decoded_andMatrixInput_2_2,decoded_decoded_andMatrixInput_3_10,decoded_decoded_andMatrixInput_4,
    decoded_decoded_andMatrixInput_5,decoded_decoded_lo_99}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_225 = &_decoded_decoded_T_224; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_226 = {decoded_decoded_andMatrixInput_0,decoded_decoded_andMatrixInput_1,
    decoded_decoded_andMatrixInput_2,decoded_decoded_andMatrixInput_3,decoded_decoded_andMatrixInput_4_18,
    decoded_decoded_andMatrixInput_5,decoded_decoded_lo_99}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_227 = &_decoded_decoded_T_226; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_228 = {decoded_decoded_andMatrixInput_0_1,decoded_decoded_andMatrixInput_1,
    decoded_decoded_andMatrixInput_2,decoded_decoded_andMatrixInput_3,decoded_decoded_andMatrixInput_4_18,
    decoded_decoded_andMatrixInput_5,decoded_decoded_lo_99}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_229 = &_decoded_decoded_T_228; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_230 = {decoded_decoded_andMatrixInput_0,decoded_decoded_andMatrixInput_0_5,
    decoded_decoded_andMatrixInput_2,decoded_decoded_andMatrixInput_3,decoded_decoded_andMatrixInput_4_18,
    decoded_decoded_andMatrixInput_5,decoded_decoded_lo_99}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_231 = &_decoded_decoded_T_230; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_232 = {decoded_decoded_andMatrixInput_0_1,decoded_decoded_andMatrixInput_0_5,
    decoded_decoded_andMatrixInput_2,decoded_decoded_andMatrixInput_3,decoded_decoded_andMatrixInput_4_18,
    decoded_decoded_andMatrixInput_5,decoded_decoded_lo_99}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_233 = &_decoded_decoded_T_232; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_234 = {decoded_decoded_andMatrixInput_0,decoded_decoded_andMatrixInput_1,
    decoded_decoded_andMatrixInput_2_2,decoded_decoded_andMatrixInput_3,decoded_decoded_andMatrixInput_4_18,
    decoded_decoded_andMatrixInput_5,decoded_decoded_lo_99}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_235 = &_decoded_decoded_T_234; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_236 = {decoded_decoded_andMatrixInput_0_1,decoded_decoded_andMatrixInput_1,
    decoded_decoded_andMatrixInput_2_2,decoded_decoded_andMatrixInput_3,decoded_decoded_andMatrixInput_4_18,
    decoded_decoded_andMatrixInput_5,decoded_decoded_lo_99}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_237 = &_decoded_decoded_T_236; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_238 = {decoded_decoded_andMatrixInput_0,decoded_decoded_andMatrixInput_0_5,
    decoded_decoded_andMatrixInput_2_2,decoded_decoded_andMatrixInput_3,decoded_decoded_andMatrixInput_4_18,
    decoded_decoded_andMatrixInput_5,decoded_decoded_lo_99}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_239 = &_decoded_decoded_T_238; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_240 = {decoded_decoded_andMatrixInput_0_1,decoded_decoded_andMatrixInput_0_5,
    decoded_decoded_andMatrixInput_2_2,decoded_decoded_andMatrixInput_3,decoded_decoded_andMatrixInput_4_18,
    decoded_decoded_andMatrixInput_5,decoded_decoded_lo_99}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_241 = &_decoded_decoded_T_240; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_242 = {decoded_decoded_andMatrixInput_0,decoded_decoded_andMatrixInput_1,
    decoded_decoded_andMatrixInput_2,decoded_decoded_andMatrixInput_3_10,decoded_decoded_andMatrixInput_4_18,
    decoded_decoded_andMatrixInput_5,decoded_decoded_lo_99}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_243 = &_decoded_decoded_T_242; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_244 = {decoded_decoded_andMatrixInput_0_1,decoded_decoded_andMatrixInput_1,
    decoded_decoded_andMatrixInput_2,decoded_decoded_andMatrixInput_3_10,decoded_decoded_andMatrixInput_4_18,
    decoded_decoded_andMatrixInput_5,decoded_decoded_lo_99}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_245 = &_decoded_decoded_T_244; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_246 = {decoded_decoded_andMatrixInput_0,decoded_decoded_andMatrixInput_0_5,
    decoded_decoded_andMatrixInput_2,decoded_decoded_andMatrixInput_3_10,decoded_decoded_andMatrixInput_4_18,
    decoded_decoded_andMatrixInput_5,decoded_decoded_lo_99}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_247 = &_decoded_decoded_T_246; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_248 = {decoded_decoded_andMatrixInput_0_1,decoded_decoded_andMatrixInput_0_5,
    decoded_decoded_andMatrixInput_2,decoded_decoded_andMatrixInput_3_10,decoded_decoded_andMatrixInput_4_18,
    decoded_decoded_andMatrixInput_5,decoded_decoded_lo_99}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_249 = &_decoded_decoded_T_248; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_250 = {decoded_decoded_andMatrixInput_0,decoded_decoded_andMatrixInput_1,
    decoded_decoded_andMatrixInput_2_2,decoded_decoded_andMatrixInput_3_10,decoded_decoded_andMatrixInput_4_18,
    decoded_decoded_andMatrixInput_5,decoded_decoded_lo_99}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_251 = &_decoded_decoded_T_250; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_252 = {decoded_decoded_andMatrixInput_0_1,decoded_decoded_andMatrixInput_1,
    decoded_decoded_andMatrixInput_2_2,decoded_decoded_andMatrixInput_3_10,decoded_decoded_andMatrixInput_4_18,
    decoded_decoded_andMatrixInput_5,decoded_decoded_lo_99}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_253 = &_decoded_decoded_T_252; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_254 = {decoded_decoded_andMatrixInput_0,decoded_decoded_andMatrixInput_0_5,
    decoded_decoded_andMatrixInput_2_2,decoded_decoded_andMatrixInput_3_10,decoded_decoded_andMatrixInput_4_18,
    decoded_decoded_andMatrixInput_5,decoded_decoded_lo_99}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_255 = &_decoded_decoded_T_254; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_256 = {decoded_decoded_andMatrixInput_0_1,decoded_decoded_andMatrixInput_0_5,
    decoded_decoded_andMatrixInput_2_2,decoded_decoded_andMatrixInput_3_10,decoded_decoded_andMatrixInput_4_18,
    decoded_decoded_andMatrixInput_5,decoded_decoded_lo_99}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_257 = &_decoded_decoded_T_256; // @[pla.scala 98:74]
  wire [4:0] decoded_decoded_lo_129 = {decoded_decoded_andMatrixInput_7,decoded_decoded_andMatrixInput_8,
    decoded_decoded_andMatrixInput_9,decoded_decoded_andMatrixInput_10_58,decoded_decoded_andMatrixInput_10_65}; // @[Cat.scala 31:58]
  wire [10:0] _decoded_decoded_T_258 = {decoded_decoded_andMatrixInput_1,decoded_decoded_andMatrixInput_2,
    decoded_decoded_andMatrixInput_3,decoded_decoded_andMatrixInput_4_18,decoded_decoded_andMatrixInput_5,
    decoded_decoded_andMatrixInput_6,decoded_decoded_lo_129}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_259 = &_decoded_decoded_T_258; // @[pla.scala 98:74]
  wire [5:0] decoded_decoded_lo_130 = {decoded_decoded_andMatrixInput_6,decoded_decoded_andMatrixInput_7,
    decoded_decoded_andMatrixInput_8,decoded_decoded_andMatrixInput_9,decoded_decoded_andMatrixInput_10_58,
    decoded_decoded_andMatrixInput_10_65}; // @[Cat.scala 31:58]
  wire [11:0] _decoded_decoded_T_260 = {decoded_decoded_andMatrixInput_0,decoded_decoded_andMatrixInput_0_5,
    decoded_decoded_andMatrixInput_2,decoded_decoded_andMatrixInput_3,decoded_decoded_andMatrixInput_4_18,
    decoded_decoded_andMatrixInput_5,decoded_decoded_lo_130}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_261 = &_decoded_decoded_T_260; // @[pla.scala 98:74]
  wire [11:0] _decoded_decoded_T_262 = {decoded_decoded_andMatrixInput_0_1,decoded_decoded_andMatrixInput_0_5,
    decoded_decoded_andMatrixInput_2,decoded_decoded_andMatrixInput_3,decoded_decoded_andMatrixInput_4_18,
    decoded_decoded_andMatrixInput_5,decoded_decoded_lo_130}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_263 = &_decoded_decoded_T_262; // @[pla.scala 98:74]
  wire [9:0] _decoded_decoded_T_264 = {decoded_decoded_andMatrixInput_2_2,decoded_decoded_andMatrixInput_3,
    decoded_decoded_andMatrixInput_4_18,decoded_decoded_andMatrixInput_5,decoded_decoded_andMatrixInput_6,
    decoded_decoded_andMatrixInput_7,decoded_decoded_andMatrixInput_8,decoded_decoded_andMatrixInput_9,
    decoded_decoded_andMatrixInput_10_58,decoded_decoded_andMatrixInput_10_65}; // @[Cat.scala 31:58]
  wire  _decoded_decoded_T_265 = &_decoded_decoded_T_264; // @[pla.scala 98:74]
  wire  _decoded_decoded_orMatrixOutputs_T = |_decoded_decoded_T_263; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_1 = |_decoded_decoded_T_259; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_2 = |_decoded_decoded_T_261; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_3 = |_decoded_decoded_T_133; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_4 = |_decoded_decoded_T_117; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_5 = |_decoded_decoded_T_115; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_6 = |_decoded_decoded_T_113; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_7 = |_decoded_decoded_T_111; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_8 = |_decoded_decoded_T_109; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_9 = |_decoded_decoded_T_107; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_10 = |_decoded_decoded_T_105; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_11 = |_decoded_decoded_T_103; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_12 = |_decoded_decoded_T_101; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_13 = |_decoded_decoded_T_99; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_14 = |_decoded_decoded_T_97; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_15 = |_decoded_decoded_T_95; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_16 = |_decoded_decoded_T_93; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_17 = |_decoded_decoded_T_91; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_18 = |_decoded_decoded_T_89; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_19 = |_decoded_decoded_T_87; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_20 = |_decoded_decoded_T_85; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_21 = |_decoded_decoded_T_83; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_22 = |_decoded_decoded_T_81; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_23 = |_decoded_decoded_T_79; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_24 = |_decoded_decoded_T_199; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_25 = |_decoded_decoded_T_197; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_26 = |_decoded_decoded_T_257; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_27 = |_decoded_decoded_T_195; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_28 = |_decoded_decoded_T_67; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_29 = |_decoded_decoded_T_255; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_30 = |_decoded_decoded_T_193; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_31 = |_decoded_decoded_T_65; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_32 = |_decoded_decoded_T_253; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_33 = |_decoded_decoded_T_191; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_34 = |_decoded_decoded_T_63; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_35 = |_decoded_decoded_T_251; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_36 = |_decoded_decoded_T_189; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_37 = |_decoded_decoded_T_61; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_38 = |_decoded_decoded_T_249; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_39 = |_decoded_decoded_T_187; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_40 = |_decoded_decoded_T_59; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_41 = |_decoded_decoded_T_247; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_42 = |_decoded_decoded_T_185; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_43 = |_decoded_decoded_T_57; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_44 = |_decoded_decoded_T_245; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_45 = |_decoded_decoded_T_183; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_46 = |_decoded_decoded_T_55; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_47 = |_decoded_decoded_T_243; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_48 = |_decoded_decoded_T_181; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_49 = |_decoded_decoded_T_53; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_50 = |_decoded_decoded_T_241; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_51 = |_decoded_decoded_T_179; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_52 = |_decoded_decoded_T_51; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_53 = |_decoded_decoded_T_239; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_54 = |_decoded_decoded_T_177; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_55 = |_decoded_decoded_T_49; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_56 = |_decoded_decoded_T_237; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_57 = |_decoded_decoded_T_175; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_58 = |_decoded_decoded_T_47; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_59 = |_decoded_decoded_T_235; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_60 = |_decoded_decoded_T_173; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_61 = |_decoded_decoded_T_45; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_62 = |_decoded_decoded_T_233; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_63 = |_decoded_decoded_T_171; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_64 = |_decoded_decoded_T_43; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_65 = |_decoded_decoded_T_231; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_66 = |_decoded_decoded_T_169; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_67 = |_decoded_decoded_T_41; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_68 = |_decoded_decoded_T_229; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_69 = |_decoded_decoded_T_167; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_70 = |_decoded_decoded_T_39; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_71 = |_decoded_decoded_T_227; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_72 = |_decoded_decoded_T_165; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_73 = |_decoded_decoded_T_37; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_74 = |_decoded_decoded_T_225; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_75 = |_decoded_decoded_T_163; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_76 = |_decoded_decoded_T_35; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_77 = |_decoded_decoded_T_223; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_78 = |_decoded_decoded_T_161; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_79 = |_decoded_decoded_T_33; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_80 = |_decoded_decoded_T_221; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_81 = |_decoded_decoded_T_159; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_82 = |_decoded_decoded_T_31; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_83 = |_decoded_decoded_T_219; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_84 = |_decoded_decoded_T_157; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_85 = |_decoded_decoded_T_29; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_86 = |_decoded_decoded_T_217; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_87 = |_decoded_decoded_T_155; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_88 = |_decoded_decoded_T_27; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_89 = |_decoded_decoded_T_215; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_90 = |_decoded_decoded_T_153; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_91 = |_decoded_decoded_T_25; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_92 = |_decoded_decoded_T_213; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_93 = |_decoded_decoded_T_151; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_94 = |_decoded_decoded_T_23; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_95 = |_decoded_decoded_T_211; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_96 = |_decoded_decoded_T_149; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_97 = |_decoded_decoded_T_21; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_98 = |_decoded_decoded_T_209; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_99 = |_decoded_decoded_T_147; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_100 = |_decoded_decoded_T_19; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_101 = |_decoded_decoded_T_207; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_102 = |_decoded_decoded_T_145; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_103 = |_decoded_decoded_T_17; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_104 = |_decoded_decoded_T_205; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_105 = |_decoded_decoded_T_143; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_106 = |_decoded_decoded_T_15; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_107 = |_decoded_decoded_T_203; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_108 = |_decoded_decoded_T_141; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_109 = |_decoded_decoded_T_13; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_110 = |_decoded_decoded_T_201; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_111 = |_decoded_decoded_T_139; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_112 = |_decoded_decoded_T_11; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_113 = |_decoded_decoded_T_137; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_114 = |_decoded_decoded_T_135; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_115 = |_decoded_decoded_T_9; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_116 = |_decoded_decoded_T_131; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_117 = |_decoded_decoded_T_129; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_118 = |_decoded_decoded_T_127; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_119 = |_decoded_decoded_T_265; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_120 = |_decoded_decoded_T_73; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_121 = |_decoded_decoded_T_75; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_122 = |_decoded_decoded_T_71; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_123 = |_decoded_decoded_T_69; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_124 = |_decoded_decoded_T_5; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_125 = |_decoded_decoded_T_77; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_126 = |_decoded_decoded_T_7; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_127 = |_decoded_decoded_T_1; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_128 = |_decoded_decoded_T_3; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_129 = |_decoded_decoded_T_125; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_130 = |_decoded_decoded_T_123; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_131 = |_decoded_decoded_T_121; // @[pla.scala 114:39]
  wire  _decoded_decoded_orMatrixOutputs_T_132 = |_decoded_decoded_T_119; // @[pla.scala 114:39]
  wire [7:0] decoded_decoded_orMatrixOutputs_lo_lo_lo_lo = {_decoded_decoded_orMatrixOutputs_T_7,
    _decoded_decoded_orMatrixOutputs_T_6,_decoded_decoded_orMatrixOutputs_T_5,_decoded_decoded_orMatrixOutputs_T_4,
    _decoded_decoded_orMatrixOutputs_T_3,_decoded_decoded_orMatrixOutputs_T_2,_decoded_decoded_orMatrixOutputs_T_1,
    _decoded_decoded_orMatrixOutputs_T}; // @[Cat.scala 31:58]
  wire [7:0] decoded_decoded_orMatrixOutputs_lo_lo_hi_lo = {_decoded_decoded_orMatrixOutputs_T_23,
    _decoded_decoded_orMatrixOutputs_T_22,_decoded_decoded_orMatrixOutputs_T_21,_decoded_decoded_orMatrixOutputs_T_20,
    _decoded_decoded_orMatrixOutputs_T_19,_decoded_decoded_orMatrixOutputs_T_18,_decoded_decoded_orMatrixOutputs_T_17,
    _decoded_decoded_orMatrixOutputs_T_16}; // @[Cat.scala 31:58]
  wire [16:0] decoded_decoded_orMatrixOutputs_lo_lo_hi = {_decoded_decoded_orMatrixOutputs_T_32,
    _decoded_decoded_orMatrixOutputs_T_31,_decoded_decoded_orMatrixOutputs_T_30,_decoded_decoded_orMatrixOutputs_T_29,
    _decoded_decoded_orMatrixOutputs_T_28,_decoded_decoded_orMatrixOutputs_T_27,_decoded_decoded_orMatrixOutputs_T_26,
    _decoded_decoded_orMatrixOutputs_T_25,_decoded_decoded_orMatrixOutputs_T_24,
    decoded_decoded_orMatrixOutputs_lo_lo_hi_lo}; // @[Cat.scala 31:58]
  wire [32:0] decoded_decoded_orMatrixOutputs_lo_lo = {decoded_decoded_orMatrixOutputs_lo_lo_hi,
    _decoded_decoded_orMatrixOutputs_T_15,_decoded_decoded_orMatrixOutputs_T_14,_decoded_decoded_orMatrixOutputs_T_13,
    _decoded_decoded_orMatrixOutputs_T_12,_decoded_decoded_orMatrixOutputs_T_11,_decoded_decoded_orMatrixOutputs_T_10,
    _decoded_decoded_orMatrixOutputs_T_9,_decoded_decoded_orMatrixOutputs_T_8,
    decoded_decoded_orMatrixOutputs_lo_lo_lo_lo}; // @[Cat.scala 31:58]
  wire [7:0] decoded_decoded_orMatrixOutputs_lo_hi_lo_lo = {_decoded_decoded_orMatrixOutputs_T_40,
    _decoded_decoded_orMatrixOutputs_T_39,_decoded_decoded_orMatrixOutputs_T_38,_decoded_decoded_orMatrixOutputs_T_37,
    _decoded_decoded_orMatrixOutputs_T_36,_decoded_decoded_orMatrixOutputs_T_35,_decoded_decoded_orMatrixOutputs_T_34,
    _decoded_decoded_orMatrixOutputs_T_33}; // @[Cat.scala 31:58]
  wire [7:0] decoded_decoded_orMatrixOutputs_lo_hi_hi_lo = {_decoded_decoded_orMatrixOutputs_T_56,
    _decoded_decoded_orMatrixOutputs_T_55,_decoded_decoded_orMatrixOutputs_T_54,_decoded_decoded_orMatrixOutputs_T_53,
    _decoded_decoded_orMatrixOutputs_T_52,_decoded_decoded_orMatrixOutputs_T_51,_decoded_decoded_orMatrixOutputs_T_50,
    _decoded_decoded_orMatrixOutputs_T_49}; // @[Cat.scala 31:58]
  wire [16:0] decoded_decoded_orMatrixOutputs_lo_hi_hi = {_decoded_decoded_orMatrixOutputs_T_65,
    _decoded_decoded_orMatrixOutputs_T_64,_decoded_decoded_orMatrixOutputs_T_63,_decoded_decoded_orMatrixOutputs_T_62,
    _decoded_decoded_orMatrixOutputs_T_61,_decoded_decoded_orMatrixOutputs_T_60,_decoded_decoded_orMatrixOutputs_T_59,
    _decoded_decoded_orMatrixOutputs_T_58,_decoded_decoded_orMatrixOutputs_T_57,
    decoded_decoded_orMatrixOutputs_lo_hi_hi_lo}; // @[Cat.scala 31:58]
  wire [32:0] decoded_decoded_orMatrixOutputs_lo_hi = {decoded_decoded_orMatrixOutputs_lo_hi_hi,
    _decoded_decoded_orMatrixOutputs_T_48,_decoded_decoded_orMatrixOutputs_T_47,_decoded_decoded_orMatrixOutputs_T_46,
    _decoded_decoded_orMatrixOutputs_T_45,_decoded_decoded_orMatrixOutputs_T_44,_decoded_decoded_orMatrixOutputs_T_43,
    _decoded_decoded_orMatrixOutputs_T_42,_decoded_decoded_orMatrixOutputs_T_41,
    decoded_decoded_orMatrixOutputs_lo_hi_lo_lo}; // @[Cat.scala 31:58]
  wire [7:0] decoded_decoded_orMatrixOutputs_hi_lo_lo_lo = {_decoded_decoded_orMatrixOutputs_T_73,
    _decoded_decoded_orMatrixOutputs_T_72,_decoded_decoded_orMatrixOutputs_T_71,_decoded_decoded_orMatrixOutputs_T_70,
    _decoded_decoded_orMatrixOutputs_T_69,_decoded_decoded_orMatrixOutputs_T_68,_decoded_decoded_orMatrixOutputs_T_67,
    _decoded_decoded_orMatrixOutputs_T_66}; // @[Cat.scala 31:58]
  wire [7:0] decoded_decoded_orMatrixOutputs_hi_lo_hi_lo = {_decoded_decoded_orMatrixOutputs_T_89,
    _decoded_decoded_orMatrixOutputs_T_88,_decoded_decoded_orMatrixOutputs_T_87,_decoded_decoded_orMatrixOutputs_T_86,
    _decoded_decoded_orMatrixOutputs_T_85,_decoded_decoded_orMatrixOutputs_T_84,_decoded_decoded_orMatrixOutputs_T_83,
    _decoded_decoded_orMatrixOutputs_T_82}; // @[Cat.scala 31:58]
  wire [16:0] decoded_decoded_orMatrixOutputs_hi_lo_hi = {_decoded_decoded_orMatrixOutputs_T_98,
    _decoded_decoded_orMatrixOutputs_T_97,_decoded_decoded_orMatrixOutputs_T_96,_decoded_decoded_orMatrixOutputs_T_95,
    _decoded_decoded_orMatrixOutputs_T_94,_decoded_decoded_orMatrixOutputs_T_93,_decoded_decoded_orMatrixOutputs_T_92,
    _decoded_decoded_orMatrixOutputs_T_91,_decoded_decoded_orMatrixOutputs_T_90,
    decoded_decoded_orMatrixOutputs_hi_lo_hi_lo}; // @[Cat.scala 31:58]
  wire [32:0] decoded_decoded_orMatrixOutputs_hi_lo = {decoded_decoded_orMatrixOutputs_hi_lo_hi,
    _decoded_decoded_orMatrixOutputs_T_81,_decoded_decoded_orMatrixOutputs_T_80,_decoded_decoded_orMatrixOutputs_T_79,
    _decoded_decoded_orMatrixOutputs_T_78,_decoded_decoded_orMatrixOutputs_T_77,_decoded_decoded_orMatrixOutputs_T_76,
    _decoded_decoded_orMatrixOutputs_T_75,_decoded_decoded_orMatrixOutputs_T_74,
    decoded_decoded_orMatrixOutputs_hi_lo_lo_lo}; // @[Cat.scala 31:58]
  wire [7:0] decoded_decoded_orMatrixOutputs_hi_hi_lo_lo = {_decoded_decoded_orMatrixOutputs_T_106,
    _decoded_decoded_orMatrixOutputs_T_105,_decoded_decoded_orMatrixOutputs_T_104,_decoded_decoded_orMatrixOutputs_T_103
    ,_decoded_decoded_orMatrixOutputs_T_102,_decoded_decoded_orMatrixOutputs_T_101,
    _decoded_decoded_orMatrixOutputs_T_100,_decoded_decoded_orMatrixOutputs_T_99}; // @[Cat.scala 31:58]
  wire [16:0] decoded_decoded_orMatrixOutputs_hi_hi_lo = {_decoded_decoded_orMatrixOutputs_T_115,
    _decoded_decoded_orMatrixOutputs_T_114,_decoded_decoded_orMatrixOutputs_T_113,_decoded_decoded_orMatrixOutputs_T_112
    ,_decoded_decoded_orMatrixOutputs_T_111,_decoded_decoded_orMatrixOutputs_T_110,
    _decoded_decoded_orMatrixOutputs_T_109,_decoded_decoded_orMatrixOutputs_T_108,_decoded_decoded_orMatrixOutputs_T_107
    ,decoded_decoded_orMatrixOutputs_hi_hi_lo_lo}; // @[Cat.scala 31:58]
  wire [7:0] decoded_decoded_orMatrixOutputs_hi_hi_hi_lo = {_decoded_decoded_orMatrixOutputs_T_123,
    _decoded_decoded_orMatrixOutputs_T_122,_decoded_decoded_orMatrixOutputs_T_121,_decoded_decoded_orMatrixOutputs_T_120
    ,_decoded_decoded_orMatrixOutputs_T_119,_decoded_decoded_orMatrixOutputs_T_118,
    _decoded_decoded_orMatrixOutputs_T_117,_decoded_decoded_orMatrixOutputs_T_116}; // @[Cat.scala 31:58]
  wire [16:0] decoded_decoded_orMatrixOutputs_hi_hi_hi = {_decoded_decoded_orMatrixOutputs_T_132,
    _decoded_decoded_orMatrixOutputs_T_131,_decoded_decoded_orMatrixOutputs_T_130,_decoded_decoded_orMatrixOutputs_T_129
    ,_decoded_decoded_orMatrixOutputs_T_128,_decoded_decoded_orMatrixOutputs_T_127,
    _decoded_decoded_orMatrixOutputs_T_126,_decoded_decoded_orMatrixOutputs_T_125,_decoded_decoded_orMatrixOutputs_T_124
    ,decoded_decoded_orMatrixOutputs_hi_hi_hi_lo}; // @[Cat.scala 31:58]
  wire [132:0] decoded_decoded_orMatrixOutputs = {decoded_decoded_orMatrixOutputs_hi_hi_hi,
    decoded_decoded_orMatrixOutputs_hi_hi_lo,decoded_decoded_orMatrixOutputs_hi_lo,decoded_decoded_orMatrixOutputs_lo_hi
    ,decoded_decoded_orMatrixOutputs_lo_lo}; // @[Cat.scala 31:58]
  wire [7:0] decoded_decoded_invMatrixOutputs_lo_lo_lo_lo = {decoded_decoded_orMatrixOutputs[7],
    decoded_decoded_orMatrixOutputs[6],decoded_decoded_orMatrixOutputs[5],decoded_decoded_orMatrixOutputs[4],
    decoded_decoded_orMatrixOutputs[3],decoded_decoded_orMatrixOutputs[2],decoded_decoded_orMatrixOutputs[1],
    decoded_decoded_orMatrixOutputs[0]}; // @[Cat.scala 31:58]
  wire [7:0] decoded_decoded_invMatrixOutputs_lo_lo_hi_lo = {decoded_decoded_orMatrixOutputs[23],
    decoded_decoded_orMatrixOutputs[22],decoded_decoded_orMatrixOutputs[21],decoded_decoded_orMatrixOutputs[20],
    decoded_decoded_orMatrixOutputs[19],decoded_decoded_orMatrixOutputs[18],decoded_decoded_orMatrixOutputs[17],
    decoded_decoded_orMatrixOutputs[16]}; // @[Cat.scala 31:58]
  wire [16:0] decoded_decoded_invMatrixOutputs_lo_lo_hi = {decoded_decoded_orMatrixOutputs[32],
    decoded_decoded_orMatrixOutputs[31],decoded_decoded_orMatrixOutputs[30],decoded_decoded_orMatrixOutputs[29],
    decoded_decoded_orMatrixOutputs[28],decoded_decoded_orMatrixOutputs[27],decoded_decoded_orMatrixOutputs[26],
    decoded_decoded_orMatrixOutputs[25],decoded_decoded_orMatrixOutputs[24],decoded_decoded_invMatrixOutputs_lo_lo_hi_lo
    }; // @[Cat.scala 31:58]
  wire [32:0] decoded_decoded_invMatrixOutputs_lo_lo = {decoded_decoded_invMatrixOutputs_lo_lo_hi,
    decoded_decoded_orMatrixOutputs[15],decoded_decoded_orMatrixOutputs[14],decoded_decoded_orMatrixOutputs[13],
    decoded_decoded_orMatrixOutputs[12],decoded_decoded_orMatrixOutputs[11],decoded_decoded_orMatrixOutputs[10],
    decoded_decoded_orMatrixOutputs[9],decoded_decoded_orMatrixOutputs[8],decoded_decoded_invMatrixOutputs_lo_lo_lo_lo}; // @[Cat.scala 31:58]
  wire [7:0] decoded_decoded_invMatrixOutputs_lo_hi_lo_lo = {decoded_decoded_orMatrixOutputs[40],
    decoded_decoded_orMatrixOutputs[39],decoded_decoded_orMatrixOutputs[38],decoded_decoded_orMatrixOutputs[37],
    decoded_decoded_orMatrixOutputs[36],decoded_decoded_orMatrixOutputs[35],decoded_decoded_orMatrixOutputs[34],
    decoded_decoded_orMatrixOutputs[33]}; // @[Cat.scala 31:58]
  wire [7:0] decoded_decoded_invMatrixOutputs_lo_hi_hi_lo = {decoded_decoded_orMatrixOutputs[56],
    decoded_decoded_orMatrixOutputs[55],decoded_decoded_orMatrixOutputs[54],decoded_decoded_orMatrixOutputs[53],
    decoded_decoded_orMatrixOutputs[52],decoded_decoded_orMatrixOutputs[51],decoded_decoded_orMatrixOutputs[50],
    decoded_decoded_orMatrixOutputs[49]}; // @[Cat.scala 31:58]
  wire [16:0] decoded_decoded_invMatrixOutputs_lo_hi_hi = {decoded_decoded_orMatrixOutputs[65],
    decoded_decoded_orMatrixOutputs[64],decoded_decoded_orMatrixOutputs[63],decoded_decoded_orMatrixOutputs[62],
    decoded_decoded_orMatrixOutputs[61],decoded_decoded_orMatrixOutputs[60],decoded_decoded_orMatrixOutputs[59],
    decoded_decoded_orMatrixOutputs[58],decoded_decoded_orMatrixOutputs[57],decoded_decoded_invMatrixOutputs_lo_hi_hi_lo
    }; // @[Cat.scala 31:58]
  wire [32:0] decoded_decoded_invMatrixOutputs_lo_hi = {decoded_decoded_invMatrixOutputs_lo_hi_hi,
    decoded_decoded_orMatrixOutputs[48],decoded_decoded_orMatrixOutputs[47],decoded_decoded_orMatrixOutputs[46],
    decoded_decoded_orMatrixOutputs[45],decoded_decoded_orMatrixOutputs[44],decoded_decoded_orMatrixOutputs[43],
    decoded_decoded_orMatrixOutputs[42],decoded_decoded_orMatrixOutputs[41],decoded_decoded_invMatrixOutputs_lo_hi_lo_lo
    }; // @[Cat.scala 31:58]
  wire [7:0] decoded_decoded_invMatrixOutputs_hi_lo_lo_lo = {decoded_decoded_orMatrixOutputs[73],
    decoded_decoded_orMatrixOutputs[72],decoded_decoded_orMatrixOutputs[71],decoded_decoded_orMatrixOutputs[70],
    decoded_decoded_orMatrixOutputs[69],decoded_decoded_orMatrixOutputs[68],decoded_decoded_orMatrixOutputs[67],
    decoded_decoded_orMatrixOutputs[66]}; // @[Cat.scala 31:58]
  wire [7:0] decoded_decoded_invMatrixOutputs_hi_lo_hi_lo = {decoded_decoded_orMatrixOutputs[89],
    decoded_decoded_orMatrixOutputs[88],decoded_decoded_orMatrixOutputs[87],decoded_decoded_orMatrixOutputs[86],
    decoded_decoded_orMatrixOutputs[85],decoded_decoded_orMatrixOutputs[84],decoded_decoded_orMatrixOutputs[83],
    decoded_decoded_orMatrixOutputs[82]}; // @[Cat.scala 31:58]
  wire [16:0] decoded_decoded_invMatrixOutputs_hi_lo_hi = {decoded_decoded_orMatrixOutputs[98],
    decoded_decoded_orMatrixOutputs[97],decoded_decoded_orMatrixOutputs[96],decoded_decoded_orMatrixOutputs[95],
    decoded_decoded_orMatrixOutputs[94],decoded_decoded_orMatrixOutputs[93],decoded_decoded_orMatrixOutputs[92],
    decoded_decoded_orMatrixOutputs[91],decoded_decoded_orMatrixOutputs[90],decoded_decoded_invMatrixOutputs_hi_lo_hi_lo
    }; // @[Cat.scala 31:58]
  wire [32:0] decoded_decoded_invMatrixOutputs_hi_lo = {decoded_decoded_invMatrixOutputs_hi_lo_hi,
    decoded_decoded_orMatrixOutputs[81],decoded_decoded_orMatrixOutputs[80],decoded_decoded_orMatrixOutputs[79],
    decoded_decoded_orMatrixOutputs[78],decoded_decoded_orMatrixOutputs[77],decoded_decoded_orMatrixOutputs[76],
    decoded_decoded_orMatrixOutputs[75],decoded_decoded_orMatrixOutputs[74],decoded_decoded_invMatrixOutputs_hi_lo_lo_lo
    }; // @[Cat.scala 31:58]
  wire [7:0] decoded_decoded_invMatrixOutputs_hi_hi_lo_lo = {decoded_decoded_orMatrixOutputs[106],
    decoded_decoded_orMatrixOutputs[105],decoded_decoded_orMatrixOutputs[104],decoded_decoded_orMatrixOutputs[103],
    decoded_decoded_orMatrixOutputs[102],decoded_decoded_orMatrixOutputs[101],decoded_decoded_orMatrixOutputs[100],
    decoded_decoded_orMatrixOutputs[99]}; // @[Cat.scala 31:58]
  wire [16:0] decoded_decoded_invMatrixOutputs_hi_hi_lo = {decoded_decoded_orMatrixOutputs[115],
    decoded_decoded_orMatrixOutputs[114],decoded_decoded_orMatrixOutputs[113],decoded_decoded_orMatrixOutputs[112],
    decoded_decoded_orMatrixOutputs[111],decoded_decoded_orMatrixOutputs[110],decoded_decoded_orMatrixOutputs[109],
    decoded_decoded_orMatrixOutputs[108],decoded_decoded_orMatrixOutputs[107],
    decoded_decoded_invMatrixOutputs_hi_hi_lo_lo}; // @[Cat.scala 31:58]
  wire [7:0] decoded_decoded_invMatrixOutputs_hi_hi_hi_lo = {decoded_decoded_orMatrixOutputs[123],
    decoded_decoded_orMatrixOutputs[122],decoded_decoded_orMatrixOutputs[121],decoded_decoded_orMatrixOutputs[120],
    decoded_decoded_orMatrixOutputs[119],decoded_decoded_orMatrixOutputs[118],decoded_decoded_orMatrixOutputs[117],
    decoded_decoded_orMatrixOutputs[116]}; // @[Cat.scala 31:58]
  wire [16:0] decoded_decoded_invMatrixOutputs_hi_hi_hi = {decoded_decoded_orMatrixOutputs[132],
    decoded_decoded_orMatrixOutputs[131],decoded_decoded_orMatrixOutputs[130],decoded_decoded_orMatrixOutputs[129],
    decoded_decoded_orMatrixOutputs[128],decoded_decoded_orMatrixOutputs[127],decoded_decoded_orMatrixOutputs[126],
    decoded_decoded_orMatrixOutputs[125],decoded_decoded_orMatrixOutputs[124],
    decoded_decoded_invMatrixOutputs_hi_hi_hi_lo}; // @[Cat.scala 31:58]
  wire [132:0] decoded_decoded_invMatrixOutputs = {decoded_decoded_invMatrixOutputs_hi_hi_hi,
    decoded_decoded_invMatrixOutputs_hi_hi_lo,decoded_decoded_invMatrixOutputs_hi_lo,
    decoded_decoded_invMatrixOutputs_lo_hi,decoded_decoded_invMatrixOutputs_lo_lo}; // @[Cat.scala 31:58]
  wire  decoded_1 = decoded_decoded_invMatrixOutputs[131]; // @[Decode.scala 50:77]
  wire  decoded_2 = decoded_decoded_invMatrixOutputs[130]; // @[Decode.scala 50:77]
  wire  decoded_4 = decoded_decoded_invMatrixOutputs[128]; // @[Decode.scala 50:77]
  wire  decoded_5 = decoded_decoded_invMatrixOutputs[127]; // @[Decode.scala 50:77]
  wire  decoded_6 = decoded_decoded_invMatrixOutputs[126]; // @[Decode.scala 50:77]
  wire  decoded_7 = decoded_decoded_invMatrixOutputs[125]; // @[Decode.scala 50:77]
  wire  decoded_8 = decoded_decoded_invMatrixOutputs[124]; // @[Decode.scala 50:77]
  wire  decoded_9 = decoded_decoded_invMatrixOutputs[123]; // @[Decode.scala 50:77]
  wire  decoded_10 = decoded_decoded_invMatrixOutputs[122]; // @[Decode.scala 50:77]
  wire  decoded_11 = decoded_decoded_invMatrixOutputs[121]; // @[Decode.scala 50:77]
  wire  decoded_12 = decoded_decoded_invMatrixOutputs[120]; // @[Decode.scala 50:77]
  wire  decoded_13 = decoded_decoded_invMatrixOutputs[119]; // @[Decode.scala 50:77]
  wire  decoded_14 = decoded_decoded_invMatrixOutputs[118]; // @[Decode.scala 50:77]
  wire  decoded_15 = decoded_decoded_invMatrixOutputs[117]; // @[Decode.scala 50:77]
  wire  decoded_16 = decoded_decoded_invMatrixOutputs[116]; // @[Decode.scala 50:77]
  wire  decoded_17 = decoded_decoded_invMatrixOutputs[115]; // @[Decode.scala 50:77]
  wire  decoded_18 = decoded_decoded_invMatrixOutputs[114]; // @[Decode.scala 50:77]
  wire  decoded_19 = decoded_decoded_invMatrixOutputs[113]; // @[Decode.scala 50:77]
  wire  decoded_107 = decoded_decoded_invMatrixOutputs[25]; // @[Decode.scala 50:77]
  wire  decoded_108 = decoded_decoded_invMatrixOutputs[24]; // @[Decode.scala 50:77]
  wire  decoded_109 = decoded_decoded_invMatrixOutputs[23]; // @[Decode.scala 50:77]
  wire  decoded_110 = decoded_decoded_invMatrixOutputs[22]; // @[Decode.scala 50:77]
  wire  decoded_113 = decoded_decoded_invMatrixOutputs[19]; // @[Decode.scala 50:77]
  wire  decoded_114 = decoded_decoded_invMatrixOutputs[18]; // @[Decode.scala 50:77]
  wire  decoded_115 = decoded_decoded_invMatrixOutputs[17]; // @[Decode.scala 50:77]
  wire  decoded_116 = decoded_decoded_invMatrixOutputs[16]; // @[Decode.scala 50:77]
  wire  decoded_117 = decoded_decoded_invMatrixOutputs[15]; // @[Decode.scala 50:77]
  wire  decoded_118 = decoded_decoded_invMatrixOutputs[14]; // @[Decode.scala 50:77]
  wire  decoded_119 = decoded_decoded_invMatrixOutputs[13]; // @[Decode.scala 50:77]
  wire  decoded_120 = decoded_decoded_invMatrixOutputs[12]; // @[Decode.scala 50:77]
  wire  decoded_129 = decoded_decoded_invMatrixOutputs[3]; // @[Decode.scala 50:77]
  wire  decoded_130 = decoded_decoded_invMatrixOutputs[2]; // @[Decode.scala 50:77]
  wire  decoded_132 = decoded_decoded_invMatrixOutputs[0]; // @[Decode.scala 50:77]
  wire [31:0] _wdata_T_1 = io_rw_cmd[1] ? io_rw_rdata : 32'h0; // @[CSR.scala 1543:9]
  wire [31:0] _wdata_T_2 = _wdata_T_1 | io_rw_wdata; // @[CSR.scala 1543:34]
  wire [31:0] _wdata_T_5 = &io_rw_cmd[1:0] ? io_rw_wdata : 32'h0; // @[CSR.scala 1543:49]
  wire [31:0] _wdata_T_6 = ~_wdata_T_5; // @[CSR.scala 1543:45]
  wire [31:0] wdata = _wdata_T_2 & _wdata_T_6; // @[CSR.scala 1543:43]
  wire  system_insn = io_rw_cmd == 3'h4; // @[CSR.scala 814:31]
  wire [31:0] _T_213 = {io_rw_addr, 20'h0}; // @[CSR.scala 830:44]
  wire [31:0] decoded_plaInput = 32'h73 | _T_213; // @[CSR.scala 830:30]
  wire [31:0] decoded_invInputs = ~decoded_plaInput; // @[pla.scala 78:21]
  wire  decoded_andMatrixInput_0 = decoded_invInputs[20]; // @[pla.scala 91:29]
  wire  decoded_andMatrixInput_1 = decoded_invInputs[21]; // @[pla.scala 91:29]
  wire  decoded_andMatrixInput_2 = decoded_invInputs[22]; // @[pla.scala 91:29]
  wire  decoded_andMatrixInput_3 = decoded_invInputs[23]; // @[pla.scala 91:29]
  wire  decoded_andMatrixInput_4 = decoded_invInputs[24]; // @[pla.scala 91:29]
  wire  decoded_andMatrixInput_5 = decoded_invInputs[25]; // @[pla.scala 91:29]
  wire  decoded_andMatrixInput_6 = decoded_invInputs[26]; // @[pla.scala 91:29]
  wire  decoded_andMatrixInput_7 = decoded_invInputs[27]; // @[pla.scala 91:29]
  wire  decoded_andMatrixInput_8 = decoded_invInputs[28]; // @[pla.scala 91:29]
  wire  decoded_andMatrixInput_9 = decoded_invInputs[29]; // @[pla.scala 91:29]
  wire  decoded_andMatrixInput_10 = decoded_invInputs[30]; // @[pla.scala 91:29]
  wire  decoded_andMatrixInput_11 = decoded_invInputs[31]; // @[pla.scala 91:29]
  wire [5:0] decoded_lo = {decoded_andMatrixInput_6,decoded_andMatrixInput_7,decoded_andMatrixInput_8,
    decoded_andMatrixInput_9,decoded_andMatrixInput_10,decoded_andMatrixInput_11}; // @[Cat.scala 31:58]
  wire [11:0] _decoded_T = {decoded_andMatrixInput_0,decoded_andMatrixInput_1,decoded_andMatrixInput_2,
    decoded_andMatrixInput_3,decoded_andMatrixInput_4,decoded_andMatrixInput_5,decoded_lo}; // @[Cat.scala 31:58]
  wire  _decoded_T_1 = &_decoded_T; // @[pla.scala 98:74]
  wire  decoded_andMatrixInput_0_1 = decoded_plaInput[20]; // @[pla.scala 90:45]
  wire [11:0] _decoded_T_2 = {decoded_andMatrixInput_0_1,decoded_andMatrixInput_1,decoded_andMatrixInput_2,
    decoded_andMatrixInput_3,decoded_andMatrixInput_4,decoded_andMatrixInput_5,decoded_lo}; // @[Cat.scala 31:58]
  wire  _decoded_T_3 = &_decoded_T_2; // @[pla.scala 98:74]
  wire  decoded_andMatrixInput_0_2 = decoded_plaInput[28]; // @[pla.scala 90:45]
  wire [3:0] _decoded_T_4 = {decoded_andMatrixInput_0_2,decoded_andMatrixInput_9,decoded_andMatrixInput_10,
    decoded_andMatrixInput_11}; // @[Cat.scala 31:58]
  wire  _decoded_T_5 = &_decoded_T_4; // @[pla.scala 98:74]
  wire  decoded_andMatrixInput_7_2 = decoded_plaInput[29]; // @[pla.scala 90:45]
  wire [9:0] _decoded_T_6 = {decoded_andMatrixInput_2,decoded_andMatrixInput_3,decoded_andMatrixInput_4,
    decoded_andMatrixInput_5,decoded_andMatrixInput_6,decoded_andMatrixInput_7,decoded_andMatrixInput_0_2,
    decoded_andMatrixInput_7_2,decoded_andMatrixInput_10,decoded_andMatrixInput_11}; // @[Cat.scala 31:58]
  wire  _decoded_T_7 = &_decoded_T_6; // @[pla.scala 98:74]
  wire  decoded_andMatrixInput_0_4 = decoded_plaInput[22]; // @[pla.scala 90:45]
  wire [9:0] _decoded_T_8 = {decoded_andMatrixInput_0_4,decoded_andMatrixInput_3,decoded_andMatrixInput_4,
    decoded_andMatrixInput_5,decoded_andMatrixInput_6,decoded_andMatrixInput_7,decoded_andMatrixInput_0_2,
    decoded_andMatrixInput_7_2,decoded_andMatrixInput_10,decoded_andMatrixInput_11}; // @[Cat.scala 31:58]
  wire  _decoded_T_9 = &_decoded_T_8; // @[pla.scala 98:74]
  wire  decoded_andMatrixInput_0_5 = decoded_plaInput[30]; // @[pla.scala 90:45]
  wire [1:0] _decoded_T_10 = {decoded_andMatrixInput_0_5,decoded_andMatrixInput_11}; // @[Cat.scala 31:58]
  wire  _decoded_T_11 = &_decoded_T_10; // @[pla.scala 98:74]
  wire  _decoded_orMatrixOutputs_T = |_decoded_T_5; // @[pla.scala 114:39]
  wire  _decoded_orMatrixOutputs_T_1 = |_decoded_T_9; // @[pla.scala 114:39]
  wire [1:0] _decoded_orMatrixOutputs_T_2 = {_decoded_T_7,_decoded_T_11}; // @[Cat.scala 31:58]
  wire  _decoded_orMatrixOutputs_T_3 = |_decoded_orMatrixOutputs_T_2; // @[pla.scala 114:39]
  wire  _decoded_orMatrixOutputs_T_4 = |_decoded_T_3; // @[pla.scala 114:39]
  wire  _decoded_orMatrixOutputs_T_5 = |_decoded_T_1; // @[pla.scala 114:39]
  wire [8:0] decoded_orMatrixOutputs = {_decoded_orMatrixOutputs_T_5,_decoded_orMatrixOutputs_T_4,
    _decoded_orMatrixOutputs_T_3,_decoded_orMatrixOutputs_T_1,_decoded_orMatrixOutputs_T,4'h0}; // @[Cat.scala 31:58]
  wire [8:0] decoded_invMatrixOutputs = {decoded_orMatrixOutputs[8],decoded_orMatrixOutputs[7],decoded_orMatrixOutputs[6
    ],decoded_orMatrixOutputs[5],decoded_orMatrixOutputs[4],decoded_orMatrixOutputs[3],decoded_orMatrixOutputs[2],
    decoded_orMatrixOutputs[1],decoded_orMatrixOutputs[0]}; // @[Cat.scala 31:58]
  wire  insn_call = system_insn & decoded_invMatrixOutputs[8]; // @[CSR.scala 831:83]
  wire  insn_break = system_insn & decoded_invMatrixOutputs[7]; // @[CSR.scala 831:83]
  wire  insn_ret = system_insn & decoded_invMatrixOutputs[6]; // @[CSR.scala 831:83]
  wire  insn_cease = system_insn & decoded_invMatrixOutputs[5]; // @[CSR.scala 831:83]
  wire  insn_wfi = system_insn & decoded_invMatrixOutputs[4]; // @[CSR.scala 831:83]
  wire [11:0] addr_1 = io_decode_0_inst[31:20]; // @[CSR.scala 835:27]
  wire [31:0] decoded_invInputs_1 = ~io_decode_0_inst; // @[pla.scala 78:21]
  wire  decoded_andMatrixInput_0_6 = decoded_invInputs_1[20]; // @[pla.scala 91:29]
  wire  decoded_andMatrixInput_1_6 = decoded_invInputs_1[21]; // @[pla.scala 91:29]
  wire  decoded_andMatrixInput_2_5 = decoded_invInputs_1[22]; // @[pla.scala 91:29]
  wire  decoded_andMatrixInput_3_5 = decoded_invInputs_1[23]; // @[pla.scala 91:29]
  wire  decoded_andMatrixInput_4_4 = decoded_invInputs_1[24]; // @[pla.scala 91:29]
  wire  decoded_andMatrixInput_5_4 = decoded_invInputs_1[25]; // @[pla.scala 91:29]
  wire  decoded_andMatrixInput_6_4 = decoded_invInputs_1[26]; // @[pla.scala 91:29]
  wire  decoded_andMatrixInput_7_4 = decoded_invInputs_1[27]; // @[pla.scala 91:29]
  wire  decoded_andMatrixInput_8_4 = decoded_invInputs_1[28]; // @[pla.scala 91:29]
  wire  decoded_andMatrixInput_9_4 = decoded_invInputs_1[29]; // @[pla.scala 91:29]
  wire  decoded_andMatrixInput_10_2 = decoded_invInputs_1[30]; // @[pla.scala 91:29]
  wire  decoded_andMatrixInput_11_2 = decoded_invInputs_1[31]; // @[pla.scala 91:29]
  wire [5:0] decoded_lo_5 = {decoded_andMatrixInput_6_4,decoded_andMatrixInput_7_4,decoded_andMatrixInput_8_4,
    decoded_andMatrixInput_9_4,decoded_andMatrixInput_10_2,decoded_andMatrixInput_11_2}; // @[Cat.scala 31:58]
  wire [11:0] _decoded_T_12 = {decoded_andMatrixInput_0_6,decoded_andMatrixInput_1_6,decoded_andMatrixInput_2_5,
    decoded_andMatrixInput_3_5,decoded_andMatrixInput_4_4,decoded_andMatrixInput_5_4,decoded_lo_5}; // @[Cat.scala 31:58]
  wire  _decoded_T_13 = &_decoded_T_12; // @[pla.scala 98:74]
  wire  decoded_andMatrixInput_0_7 = io_decode_0_inst[20]; // @[pla.scala 90:45]
  wire [11:0] _decoded_T_14 = {decoded_andMatrixInput_0_7,decoded_andMatrixInput_1_6,decoded_andMatrixInput_2_5,
    decoded_andMatrixInput_3_5,decoded_andMatrixInput_4_4,decoded_andMatrixInput_5_4,decoded_lo_5}; // @[Cat.scala 31:58]
  wire  _decoded_T_15 = &_decoded_T_14; // @[pla.scala 98:74]
  wire  decoded_andMatrixInput_0_8 = io_decode_0_inst[28]; // @[pla.scala 90:45]
  wire [3:0] _decoded_T_16 = {decoded_andMatrixInput_0_8,decoded_andMatrixInput_9_4,decoded_andMatrixInput_10_2,
    decoded_andMatrixInput_11_2}; // @[Cat.scala 31:58]
  wire  _decoded_T_17 = &_decoded_T_16; // @[pla.scala 98:74]
  wire  decoded_andMatrixInput_7_6 = io_decode_0_inst[29]; // @[pla.scala 90:45]
  wire [9:0] _decoded_T_18 = {decoded_andMatrixInput_2_5,decoded_andMatrixInput_3_5,decoded_andMatrixInput_4_4,
    decoded_andMatrixInput_5_4,decoded_andMatrixInput_6_4,decoded_andMatrixInput_7_4,decoded_andMatrixInput_0_8,
    decoded_andMatrixInput_7_6,decoded_andMatrixInput_10_2,decoded_andMatrixInput_11_2}; // @[Cat.scala 31:58]
  wire  _decoded_T_19 = &_decoded_T_18; // @[pla.scala 98:74]
  wire  decoded_andMatrixInput_0_10 = io_decode_0_inst[22]; // @[pla.scala 90:45]
  wire [9:0] _decoded_T_20 = {decoded_andMatrixInput_0_10,decoded_andMatrixInput_3_5,decoded_andMatrixInput_4_4,
    decoded_andMatrixInput_5_4,decoded_andMatrixInput_6_4,decoded_andMatrixInput_7_4,decoded_andMatrixInput_0_8,
    decoded_andMatrixInput_7_6,decoded_andMatrixInput_10_2,decoded_andMatrixInput_11_2}; // @[Cat.scala 31:58]
  wire  _decoded_T_21 = &_decoded_T_20; // @[pla.scala 98:74]
  wire  decoded_andMatrixInput_0_11 = io_decode_0_inst[30]; // @[pla.scala 90:45]
  wire [1:0] _decoded_T_22 = {decoded_andMatrixInput_0_11,decoded_andMatrixInput_11_2}; // @[Cat.scala 31:58]
  wire  _decoded_T_23 = &_decoded_T_22; // @[pla.scala 98:74]
  wire  _decoded_orMatrixOutputs_T_6 = |_decoded_T_17; // @[pla.scala 114:39]
  wire  _decoded_orMatrixOutputs_T_7 = |_decoded_T_21; // @[pla.scala 114:39]
  wire [1:0] _decoded_orMatrixOutputs_T_8 = {_decoded_T_19,_decoded_T_23}; // @[Cat.scala 31:58]
  wire  _decoded_orMatrixOutputs_T_9 = |_decoded_orMatrixOutputs_T_8; // @[pla.scala 114:39]
  wire  _decoded_orMatrixOutputs_T_10 = |_decoded_T_15; // @[pla.scala 114:39]
  wire  _decoded_orMatrixOutputs_T_11 = |_decoded_T_13; // @[pla.scala 114:39]
  wire [8:0] decoded_orMatrixOutputs_1 = {_decoded_orMatrixOutputs_T_11,_decoded_orMatrixOutputs_T_10,
    _decoded_orMatrixOutputs_T_9,_decoded_orMatrixOutputs_T_7,_decoded_orMatrixOutputs_T_6,4'h0}; // @[Cat.scala 31:58]
  wire [8:0] decoded_invMatrixOutputs_1 = {decoded_orMatrixOutputs_1[8],decoded_orMatrixOutputs_1[7],
    decoded_orMatrixOutputs_1[6],decoded_orMatrixOutputs_1[5],decoded_orMatrixOutputs_1[4],decoded_orMatrixOutputs_1[3],
    decoded_orMatrixOutputs_1[2],decoded_orMatrixOutputs_1[1],decoded_orMatrixOutputs_1[0]}; // @[Cat.scala 31:58]
  wire  is_ret = decoded_invMatrixOutputs_1[6]; // @[Decode.scala 50:77]
  wire [11:0] io_decode_0_fp_csr_invInputs = ~addr_1; // @[pla.scala 78:21]
  wire  _csr_exists_T_15 = addr_1 == 12'h7b1; // @[CSR.scala 837:93]
  wire  _csr_exists_T_147 = addr_1 == 12'h7a0 | addr_1 == 12'h7a1 | addr_1 == 12'h7a2 | addr_1 == 12'h7a3 | addr_1 == 12'h301
     | addr_1 == 12'h300 | addr_1 == 12'h305 | addr_1 == 12'h344 | addr_1 == 12'h304 | addr_1 == 12'h340 | addr_1 == 12'h341
     | addr_1 == 12'h343 | addr_1 == 12'h342 | addr_1 == 12'hf14 | addr_1 == 12'h7b0 | _csr_exists_T_15; // @[CSR.scala 837:109]
  wire  _csr_exists_T_162 = _csr_exists_T_147 | addr_1 == 12'h7b2 | addr_1 == 12'h320 | addr_1 == 12'hb00 | addr_1 == 12'hb02
     | addr_1 == 12'h323 | addr_1 == 12'hb03 | addr_1 == 12'hb83 | addr_1 == 12'h324 | addr_1 == 12'hb04 | addr_1 == 12'hb84
     | addr_1 == 12'h325 | addr_1 == 12'hb05 | addr_1 == 12'hb85 | addr_1 == 12'h326 | addr_1 == 12'hb06; // @[CSR.scala 837:109]
  wire  _csr_exists_T_177 = _csr_exists_T_162 | addr_1 == 12'hb86 | addr_1 == 12'h327 | addr_1 == 12'hb07 | addr_1 == 12'hb87
     | addr_1 == 12'h328 | addr_1 == 12'hb08 | addr_1 == 12'hb88 | addr_1 == 12'h329 | addr_1 == 12'hb09 | addr_1 == 12'hb89
     | addr_1 == 12'h32a | addr_1 == 12'hb0a | addr_1 == 12'hb8a | addr_1 == 12'h32b | addr_1 == 12'hb0b; // @[CSR.scala 837:109]
  wire  _csr_exists_T_192 = _csr_exists_T_177 | addr_1 == 12'hb8b | addr_1 == 12'h32c | addr_1 == 12'hb0c | addr_1 == 12'hb8c
     | addr_1 == 12'h32d | addr_1 == 12'hb0d | addr_1 == 12'hb8d | addr_1 == 12'h32e | addr_1 == 12'hb0e | addr_1 == 12'hb8e
     | addr_1 == 12'h32f | addr_1 == 12'hb0f | addr_1 == 12'hb8f | addr_1 == 12'h330 | addr_1 == 12'hb10; // @[CSR.scala 837:109]
  wire  _csr_exists_T_207 = _csr_exists_T_192 | addr_1 == 12'hb90 | addr_1 == 12'h331 | addr_1 == 12'hb11 | addr_1 == 12'hb91
     | addr_1 == 12'h332 | addr_1 == 12'hb12 | addr_1 == 12'hb92 | addr_1 == 12'h333 | addr_1 == 12'hb13 | addr_1 == 12'hb93
     | addr_1 == 12'h334 | addr_1 == 12'hb14 | addr_1 == 12'hb94 | addr_1 == 12'h335 | addr_1 == 12'hb15; // @[CSR.scala 837:109]
  wire  _csr_exists_T_222 = _csr_exists_T_207 | addr_1 == 12'hb95 | addr_1 == 12'h336 | addr_1 == 12'hb16 | addr_1 == 12'hb96
     | addr_1 == 12'h337 | addr_1 == 12'hb17 | addr_1 == 12'hb97 | addr_1 == 12'h338 | addr_1 == 12'hb18 | addr_1 == 12'hb98
     | addr_1 == 12'h339 | addr_1 == 12'hb19 | addr_1 == 12'hb99 | addr_1 == 12'h33a | addr_1 == 12'hb1a; // @[CSR.scala 837:109]
  wire  _csr_exists_T_237 = _csr_exists_T_222 | addr_1 == 12'hb9a | addr_1 == 12'h33b | addr_1 == 12'hb1b | addr_1 == 12'hb9b
     | addr_1 == 12'h33c | addr_1 == 12'hb1c | addr_1 == 12'hb9c | addr_1 == 12'h33d | addr_1 == 12'hb1d | addr_1 == 12'hb9d
     | addr_1 == 12'h33e | addr_1 == 12'hb1e | addr_1 == 12'hb9e | addr_1 == 12'h33f | addr_1 == 12'hb1f; // @[CSR.scala 837:109]
  wire  _csr_exists_T_252 = _csr_exists_T_237 | addr_1 == 12'hb9f | addr_1 == 12'hb80 | addr_1 == 12'hb82 | addr_1 == 12'h3a0
     | addr_1 == 12'h3a1 | addr_1 == 12'h3a2 | addr_1 == 12'h3a3 | addr_1 == 12'h3b0 | addr_1 == 12'h3b1 | addr_1 == 12'h3b2
     | addr_1 == 12'h3b3 | addr_1 == 12'h3b4 | addr_1 == 12'h3b5 | addr_1 == 12'h3b6 | addr_1 == 12'h3b7; // @[CSR.scala 837:109]
  wire  csr_exists = _csr_exists_T_252 | addr_1 == 12'h3b8 | addr_1 == 12'h3b9 | addr_1 == 12'h3ba | addr_1 == 12'h3bb
     | addr_1 == 12'h3bc | addr_1 == 12'h3bd | addr_1 == 12'h3be | addr_1 == 12'h3bf | addr_1 == 12'h7c1 | addr_1 == 12'hf12
     | addr_1 == 12'hf11 | addr_1 == 12'hf13; // @[CSR.scala 837:109]
  wire  _io_decode_0_read_illegal_T_1 = ~csr_exists; // @[CSR.scala 861:7]
  wire  io_decode_0_read_illegal_andMatrixInput_0 = addr_1[4]; // @[pla.scala 90:45]
  wire  io_decode_0_read_illegal_andMatrixInput_1 = addr_1[5]; // @[pla.scala 90:45]
  wire  io_decode_0_read_illegal_andMatrixInput_2 = io_decode_0_fp_csr_invInputs[6]; // @[pla.scala 91:29]
  wire  io_decode_0_read_illegal_andMatrixInput_3 = addr_1[7]; // @[pla.scala 90:45]
  wire  io_decode_0_read_illegal_andMatrixInput_4 = addr_1[8]; // @[pla.scala 90:45]
  wire  io_decode_0_read_illegal_andMatrixInput_5 = addr_1[9]; // @[pla.scala 90:45]
  wire  io_decode_0_read_illegal_andMatrixInput_6 = addr_1[10]; // @[pla.scala 90:45]
  wire  io_decode_0_read_illegal_andMatrixInput_7 = io_decode_0_fp_csr_invInputs[11]; // @[pla.scala 91:29]
  wire [7:0] _io_decode_0_read_illegal_T_12 = {io_decode_0_read_illegal_andMatrixInput_0,
    io_decode_0_read_illegal_andMatrixInput_1,io_decode_0_read_illegal_andMatrixInput_2,
    io_decode_0_read_illegal_andMatrixInput_3,io_decode_0_read_illegal_andMatrixInput_4,
    io_decode_0_read_illegal_andMatrixInput_5,io_decode_0_read_illegal_andMatrixInput_6,
    io_decode_0_read_illegal_andMatrixInput_7}; // @[Cat.scala 31:58]
  wire  _io_decode_0_read_illegal_T_13 = &_io_decode_0_read_illegal_T_12; // @[pla.scala 98:74]
  wire  io_decode_0_read_illegal_orMatrixOutputs = |_io_decode_0_read_illegal_T_13; // @[pla.scala 114:39]
  wire  _io_decode_0_read_illegal_T_15 = ~reg_debug; // @[CSR.scala 864:45]
  wire  _io_decode_0_read_illegal_T_16 = io_decode_0_read_illegal_orMatrixOutputs & ~reg_debug; // @[CSR.scala 864:42]
  wire  _io_decode_0_read_illegal_T_17 = _io_decode_0_read_illegal_T_1 | _io_decode_0_read_illegal_T_16; // @[CSR.scala 863:36]
  wire  _io_decode_0_read_illegal_T_21 = io_decode_0_fp_csr & io_decode_0_fp_illegal; // @[CSR.scala 866:21]
  wire [11:0] io_decode_0_write_flush_addr_m = addr_1 | 12'h300; // @[CSR.scala 869:25]
  wire [31:0] _cause_T_5 = insn_break ? 32'h3 : io_cause; // @[CSR.scala 897:14]
  wire [31:0] cause = insn_call ? 32'hb : _cause_T_5; // @[CSR.scala 896:8]
  wire [7:0] cause_lsbs = cause[7:0]; // @[CSR.scala 898:25]
  wire  _causeIsDebugInt_T_1 = cause_lsbs == 8'he; // @[CSR.scala 899:53]
  wire  causeIsDebugInt = cause[31] & cause_lsbs == 8'he; // @[CSR.scala 899:39]
  wire  _causeIsDebugTrigger_T_1 = ~cause[31]; // @[CSR.scala 900:29]
  wire  causeIsDebugTrigger = ~cause[31] & _causeIsDebugInt_T_1; // @[CSR.scala 900:44]
  wire [3:0] _causeIsDebugBreak_T_3 = {reg_dcsr_ebreakm,1'h0,2'h0}; // @[Cat.scala 31:58]
  wire [3:0] _causeIsDebugBreak_T_4 = {{3'd0}, _causeIsDebugBreak_T_3[3]}; // @[CSR.scala 901:134]
  wire  causeIsDebugBreak = _causeIsDebugTrigger_T_1 & insn_break & _causeIsDebugBreak_T_4[0]; // @[CSR.scala 901:56]
  wire  trapToDebug = reg_singleStepped | causeIsDebugInt | causeIsDebugTrigger | causeIsDebugBreak | reg_debug; // @[CSR.scala 902:123]
  wire [11:0] _debugTVec_T = insn_break ? 12'h800 : 12'h808; // @[CSR.scala 905:37]
  wire [11:0] debugTVec = reg_debug ? _debugTVec_T : 12'h800; // @[CSR.scala 905:22]
  wire [6:0] notDebugTVec_interruptOffset = {cause[4:0], 2'h0}; // @[CSR.scala 915:59]
  wire [31:0] notDebugTVec_interruptVec = {read_mtvec[31:7],notDebugTVec_interruptOffset}; // @[Cat.scala 31:58]
  wire  notDebugTVec_doVector = read_mtvec[0] & cause[31] & cause_lsbs[7:5] == 3'h0; // @[CSR.scala 917:55]
  wire [31:0] _notDebugTVec_T_1 = {read_mtvec[31:2], 2'h0}; // @[CSR.scala 918:56]
  wire [31:0] notDebugTVec = notDebugTVec_doVector ? notDebugTVec_interruptVec : _notDebugTVec_T_1; // @[CSR.scala 918:8]
  wire [31:0] tvec = trapToDebug ? {{20'd0}, debugTVec} : notDebugTVec; // @[CSR.scala 931:17]
  wire  _io_eret_T = insn_call | insn_break; // @[CSR.scala 936:24]
  wire  exception = _io_eret_T | io_exception; // @[CSR.scala 956:43]
  wire [1:0] _T_248 = insn_ret + insn_call; // @[Bitwise.scala 48:55]
  wire [1:0] _T_250 = insn_break + io_exception; // @[Bitwise.scala 48:55]
  wire [2:0] _T_252 = _T_248 + _T_250; // @[Bitwise.scala 48:55]
  wire  _T_256 = ~reset; // @[CSR.scala 957:9]
  wire  _GEN_46 = insn_wfi & _io_interrupt_T & _io_decode_0_read_illegal_T_15 | reg_wfi; // @[CSR.scala 539:50 959:{51,61}]
  wire  _GEN_48 = io_retire | exception | reg_singleStepped; // @[CSR.scala 454:30 963:{36,56}]
  wire [31:0] _epc_T = ~io_pc; // @[CSR.scala 1564:28]
  wire [31:0] _epc_T_1 = _epc_T | 32'h1; // @[CSR.scala 1564:31]
  wire [31:0] epc = ~_epc_T_1; // @[CSR.scala 1564:26]
  wire [1:0] _reg_dcsr_cause_T = causeIsDebugTrigger ? 2'h2 : 2'h1; // @[CSR.scala 976:86]
  wire [1:0] _reg_dcsr_cause_T_1 = causeIsDebugInt ? 2'h3 : _reg_dcsr_cause_T; // @[CSR.scala 976:56]
  wire [2:0] _reg_dcsr_cause_T_2 = reg_singleStepped ? 3'h4 : {{1'd0}, _reg_dcsr_cause_T_1}; // @[CSR.scala 976:30]
  wire  _GEN_51 = _io_decode_0_read_illegal_T_15 | reg_debug; // @[CSR.scala 972:25 974:19 450:22]
  wire [31:0] _GEN_52 = _io_decode_0_read_illegal_T_15 ? epc : reg_dpc; // @[CSR.scala 972:25 975:17 451:20]
  wire [1:0] _GEN_73 = {{1'd0}, reg_mstatus_spp}; // @[CSR.scala 1000:35 1010:23 370:24]
  wire  _GEN_145 = trapToDebug ? _GEN_51 : reg_debug; // @[CSR.scala 450:22 971:24]
  wire [31:0] _GEN_146 = trapToDebug ? _GEN_52 : reg_dpc; // @[CSR.scala 451:20 971:24]
  wire [1:0] _GEN_170 = trapToDebug ? {{1'd0}, reg_mstatus_spp} : _GEN_73; // @[CSR.scala 370:24 971:24]
  wire [31:0] _GEN_174 = trapToDebug ? reg_mepc : epc; // @[CSR.scala 473:21 971:24]
  wire [31:0] _GEN_175 = trapToDebug ? reg_mcause : cause; // @[CSR.scala 971:24 474:27]
  wire [31:0] _GEN_176 = trapToDebug ? reg_mtval : io_tval; // @[CSR.scala 475:22 971:24]
  wire  _GEN_178 = trapToDebug ? reg_mstatus_mpie : reg_mstatus_mie; // @[CSR.scala 370:24 971:24]
  wire  _GEN_180 = trapToDebug & reg_mstatus_mie; // @[CSR.scala 370:24 971:24]
  wire  _GEN_182 = exception ? _GEN_145 : reg_debug; // @[CSR.scala 970:20 450:22]
  wire [31:0] _GEN_183 = exception ? _GEN_146 : reg_dpc; // @[CSR.scala 451:20 970:20]
  wire [1:0] _GEN_207 = exception ? _GEN_170 : {{1'd0}, reg_mstatus_spp}; // @[CSR.scala 970:20 370:24]
  wire [31:0] _GEN_211 = exception ? _GEN_174 : reg_mepc; // @[CSR.scala 970:20 473:21]
  wire [31:0] _GEN_212 = exception ? _GEN_175 : reg_mcause; // @[CSR.scala 970:20 474:27]
  wire [31:0] _GEN_213 = exception ? _GEN_176 : reg_mtval; // @[CSR.scala 970:20 475:22]
  wire  _GEN_215 = exception ? _GEN_178 : reg_mstatus_mpie; // @[CSR.scala 970:20 370:24]
  wire  _GEN_217 = exception ? _GEN_180 : reg_mstatus_mie; // @[CSR.scala 970:20 370:24]
  wire [31:0] _GEN_239 = io_rw_addr[10] & io_rw_addr[7] ? _T_28 : _T_22; // @[CSR.scala 1067:70 1071:15]
  wire  _GEN_241 = io_rw_addr[10] & io_rw_addr[7] ? _GEN_217 : reg_mstatus_mpie; // @[CSR.scala 1067:70]
  wire  _GEN_242 = io_rw_addr[10] & io_rw_addr[7] ? _GEN_215 : 1'h1; // @[CSR.scala 1067:70]
  wire  _GEN_273 = insn_ret ? _GEN_241 : _GEN_217; // @[CSR.scala 1048:19]
  wire  _GEN_274 = insn_ret ? _GEN_242 : _GEN_215; // @[CSR.scala 1048:19]
  reg  io_status_cease_r; // @[Reg.scala 28:20]
  wire  _GEN_279 = insn_cease | io_status_cease_r; // @[Reg.scala 29:18 28:20 29:22]
  wire [31:0] _io_rw_rdata_T_1 = decoded_1 ? _T_16 : 32'h0; // @[Mux.scala 27:73]
  wire [31:0] _io_rw_rdata_T_2 = decoded_2 ? reg_bp_0_address : 32'h0; // @[Mux.scala 27:73]
  wire [31:0] _io_rw_rdata_T_4 = decoded_4 ? reg_misa : 32'h0; // @[Mux.scala 27:73]
  wire [31:0] _io_rw_rdata_T_5 = decoded_5 ? read_mstatus : 32'h0; // @[Mux.scala 27:73]
  wire [31:0] _io_rw_rdata_T_6 = decoded_6 ? read_mtvec : 32'h0; // @[Mux.scala 27:73]
  wire [15:0] _io_rw_rdata_T_7 = decoded_7 ? read_mip : 16'h0; // @[Mux.scala 27:73]
  wire [31:0] _io_rw_rdata_T_8 = decoded_8 ? reg_mie : 32'h0; // @[Mux.scala 27:73]
  wire [31:0] _io_rw_rdata_T_9 = decoded_9 ? reg_mscratch : 32'h0; // @[Mux.scala 27:73]
  wire [31:0] _io_rw_rdata_T_10 = decoded_10 ? _T_22 : 32'h0; // @[Mux.scala 27:73]
  wire [31:0] _io_rw_rdata_T_11 = decoded_11 ? reg_mtval : 32'h0; // @[Mux.scala 27:73]
  wire [31:0] _io_rw_rdata_T_12 = decoded_12 ? reg_mcause : 32'h0; // @[Mux.scala 27:73]
  wire  _io_rw_rdata_T_13 = decoded_13 & io_hartid; // @[Mux.scala 27:73]
  wire [31:0] _io_rw_rdata_T_14 = decoded_14 ? _T_23 : 32'h0; // @[Mux.scala 27:73]
  wire [31:0] _io_rw_rdata_T_15 = decoded_15 ? _T_28 : 32'h0; // @[Mux.scala 27:73]
  wire [31:0] _io_rw_rdata_T_16 = decoded_16 ? reg_dscratch0 : 32'h0; // @[Mux.scala 27:73]
  wire [2:0] _io_rw_rdata_T_17 = decoded_17 ? reg_mcountinhibit : 3'h0; // @[Mux.scala 27:73]
  wire [63:0] _io_rw_rdata_T_18 = decoded_18 ? value_1 : 64'h0; // @[Mux.scala 27:73]
  wire [63:0] _io_rw_rdata_T_19 = decoded_19 ? value : 64'h0; // @[Mux.scala 27:73]
  wire [31:0] _io_rw_rdata_T_107 = decoded_107 ? value_1[63:32] : 32'h0; // @[Mux.scala 27:73]
  wire [31:0] _io_rw_rdata_T_108 = decoded_108 ? value[63:32] : 32'h0; // @[Mux.scala 27:73]
  wire [31:0] _io_rw_rdata_T_109 = decoded_109 ? _T_64 : 32'h0; // @[Mux.scala 27:73]
  wire [31:0] _io_rw_rdata_T_110 = decoded_110 ? _T_69 : 32'h0; // @[Mux.scala 27:73]
  wire [29:0] _io_rw_rdata_T_113 = decoded_113 ? reg_pmp_0_addr : 30'h0; // @[Mux.scala 27:73]
  wire [29:0] _io_rw_rdata_T_114 = decoded_114 ? reg_pmp_1_addr : 30'h0; // @[Mux.scala 27:73]
  wire [29:0] _io_rw_rdata_T_115 = decoded_115 ? reg_pmp_2_addr : 30'h0; // @[Mux.scala 27:73]
  wire [29:0] _io_rw_rdata_T_116 = decoded_116 ? reg_pmp_3_addr : 30'h0; // @[Mux.scala 27:73]
  wire [29:0] _io_rw_rdata_T_117 = decoded_117 ? reg_pmp_4_addr : 30'h0; // @[Mux.scala 27:73]
  wire [29:0] _io_rw_rdata_T_118 = decoded_118 ? reg_pmp_5_addr : 30'h0; // @[Mux.scala 27:73]
  wire [29:0] _io_rw_rdata_T_119 = decoded_119 ? reg_pmp_6_addr : 30'h0; // @[Mux.scala 27:73]
  wire [29:0] _io_rw_rdata_T_120 = decoded_120 ? reg_pmp_7_addr : 30'h0; // @[Mux.scala 27:73]
  wire [31:0] _io_rw_rdata_T_129 = decoded_129 ? reg_custom_0 : 32'h0; // @[Mux.scala 27:73]
  wire [31:0] _io_rw_rdata_T_130 = decoded_130 ? 32'h1 : 32'h0; // @[Mux.scala 27:73]
  wire [31:0] _io_rw_rdata_T_132 = decoded_132 ? 32'h20181004 : 32'h0; // @[Mux.scala 27:73]
  wire [31:0] _io_rw_rdata_T_134 = _io_rw_rdata_T_1 | _io_rw_rdata_T_2; // @[Mux.scala 27:73]
  wire [31:0] _io_rw_rdata_T_136 = _io_rw_rdata_T_134 | _io_rw_rdata_T_4; // @[Mux.scala 27:73]
  wire [31:0] _io_rw_rdata_T_137 = _io_rw_rdata_T_136 | _io_rw_rdata_T_5; // @[Mux.scala 27:73]
  wire [31:0] _io_rw_rdata_T_138 = _io_rw_rdata_T_137 | _io_rw_rdata_T_6; // @[Mux.scala 27:73]
  wire [31:0] _GEN_592 = {{16'd0}, _io_rw_rdata_T_7}; // @[Mux.scala 27:73]
  wire [31:0] _io_rw_rdata_T_139 = _io_rw_rdata_T_138 | _GEN_592; // @[Mux.scala 27:73]
  wire [31:0] _io_rw_rdata_T_140 = _io_rw_rdata_T_139 | _io_rw_rdata_T_8; // @[Mux.scala 27:73]
  wire [31:0] _io_rw_rdata_T_141 = _io_rw_rdata_T_140 | _io_rw_rdata_T_9; // @[Mux.scala 27:73]
  wire [31:0] _io_rw_rdata_T_142 = _io_rw_rdata_T_141 | _io_rw_rdata_T_10; // @[Mux.scala 27:73]
  wire [31:0] _io_rw_rdata_T_143 = _io_rw_rdata_T_142 | _io_rw_rdata_T_11; // @[Mux.scala 27:73]
  wire [31:0] _io_rw_rdata_T_144 = _io_rw_rdata_T_143 | _io_rw_rdata_T_12; // @[Mux.scala 27:73]
  wire [31:0] _GEN_593 = {{31'd0}, _io_rw_rdata_T_13}; // @[Mux.scala 27:73]
  wire [31:0] _io_rw_rdata_T_145 = _io_rw_rdata_T_144 | _GEN_593; // @[Mux.scala 27:73]
  wire [31:0] _io_rw_rdata_T_146 = _io_rw_rdata_T_145 | _io_rw_rdata_T_14; // @[Mux.scala 27:73]
  wire [31:0] _io_rw_rdata_T_147 = _io_rw_rdata_T_146 | _io_rw_rdata_T_15; // @[Mux.scala 27:73]
  wire [31:0] _io_rw_rdata_T_148 = _io_rw_rdata_T_147 | _io_rw_rdata_T_16; // @[Mux.scala 27:73]
  wire [31:0] _GEN_594 = {{29'd0}, _io_rw_rdata_T_17}; // @[Mux.scala 27:73]
  wire [31:0] _io_rw_rdata_T_149 = _io_rw_rdata_T_148 | _GEN_594; // @[Mux.scala 27:73]
  wire [63:0] _GEN_595 = {{32'd0}, _io_rw_rdata_T_149}; // @[Mux.scala 27:73]
  wire [63:0] _io_rw_rdata_T_150 = _GEN_595 | _io_rw_rdata_T_18; // @[Mux.scala 27:73]
  wire [63:0] _io_rw_rdata_T_151 = _io_rw_rdata_T_150 | _io_rw_rdata_T_19; // @[Mux.scala 27:73]
  wire [63:0] _GEN_596 = {{32'd0}, _io_rw_rdata_T_107}; // @[Mux.scala 27:73]
  wire [63:0] _io_rw_rdata_T_239 = _io_rw_rdata_T_151 | _GEN_596; // @[Mux.scala 27:73]
  wire [63:0] _GEN_597 = {{32'd0}, _io_rw_rdata_T_108}; // @[Mux.scala 27:73]
  wire [63:0] _io_rw_rdata_T_240 = _io_rw_rdata_T_239 | _GEN_597; // @[Mux.scala 27:73]
  wire [63:0] _GEN_598 = {{32'd0}, _io_rw_rdata_T_109}; // @[Mux.scala 27:73]
  wire [63:0] _io_rw_rdata_T_241 = _io_rw_rdata_T_240 | _GEN_598; // @[Mux.scala 27:73]
  wire [63:0] _GEN_599 = {{32'd0}, _io_rw_rdata_T_110}; // @[Mux.scala 27:73]
  wire [63:0] _io_rw_rdata_T_242 = _io_rw_rdata_T_241 | _GEN_599; // @[Mux.scala 27:73]
  wire [63:0] _GEN_600 = {{34'd0}, _io_rw_rdata_T_113}; // @[Mux.scala 27:73]
  wire [63:0] _io_rw_rdata_T_245 = _io_rw_rdata_T_242 | _GEN_600; // @[Mux.scala 27:73]
  wire [63:0] _GEN_601 = {{34'd0}, _io_rw_rdata_T_114}; // @[Mux.scala 27:73]
  wire [63:0] _io_rw_rdata_T_246 = _io_rw_rdata_T_245 | _GEN_601; // @[Mux.scala 27:73]
  wire [63:0] _GEN_602 = {{34'd0}, _io_rw_rdata_T_115}; // @[Mux.scala 27:73]
  wire [63:0] _io_rw_rdata_T_247 = _io_rw_rdata_T_246 | _GEN_602; // @[Mux.scala 27:73]
  wire [63:0] _GEN_603 = {{34'd0}, _io_rw_rdata_T_116}; // @[Mux.scala 27:73]
  wire [63:0] _io_rw_rdata_T_248 = _io_rw_rdata_T_247 | _GEN_603; // @[Mux.scala 27:73]
  wire [63:0] _GEN_604 = {{34'd0}, _io_rw_rdata_T_117}; // @[Mux.scala 27:73]
  wire [63:0] _io_rw_rdata_T_249 = _io_rw_rdata_T_248 | _GEN_604; // @[Mux.scala 27:73]
  wire [63:0] _GEN_605 = {{34'd0}, _io_rw_rdata_T_118}; // @[Mux.scala 27:73]
  wire [63:0] _io_rw_rdata_T_250 = _io_rw_rdata_T_249 | _GEN_605; // @[Mux.scala 27:73]
  wire [63:0] _GEN_606 = {{34'd0}, _io_rw_rdata_T_119}; // @[Mux.scala 27:73]
  wire [63:0] _io_rw_rdata_T_251 = _io_rw_rdata_T_250 | _GEN_606; // @[Mux.scala 27:73]
  wire [63:0] _GEN_607 = {{34'd0}, _io_rw_rdata_T_120}; // @[Mux.scala 27:73]
  wire [63:0] _io_rw_rdata_T_252 = _io_rw_rdata_T_251 | _GEN_607; // @[Mux.scala 27:73]
  wire [63:0] _GEN_608 = {{32'd0}, _io_rw_rdata_T_129}; // @[Mux.scala 27:73]
  wire [63:0] _io_rw_rdata_T_261 = _io_rw_rdata_T_252 | _GEN_608; // @[Mux.scala 27:73]
  wire [63:0] _GEN_609 = {{32'd0}, _io_rw_rdata_T_130}; // @[Mux.scala 27:73]
  wire [63:0] _io_rw_rdata_T_262 = _io_rw_rdata_T_261 | _GEN_609; // @[Mux.scala 27:73]
  wire [63:0] _GEN_610 = {{32'd0}, _io_rw_rdata_T_132}; // @[Mux.scala 27:73]
  wire [63:0] _io_rw_rdata_T_264 = _io_rw_rdata_T_262 | _GEN_610; // @[Mux.scala 27:73]
  wire  _T_400 = io_rw_cmd == 3'h5; // @[package.scala 15:47]
  wire  _T_401 = io_rw_cmd == 3'h6; // @[package.scala 15:47]
  wire  _T_402 = io_rw_cmd == 3'h7; // @[package.scala 15:47]
  wire  csr_wen = _T_401 | _T_402 | _T_400; // @[package.scala 72:59]
  wire [104:0] _new_mstatus_WIRE = {{73'd0}, wdata};
  wire  new_mstatus_mie = _new_mstatus_WIRE[3]; // @[CSR.scala 1156:47]
  wire  new_mstatus_mpie = _new_mstatus_WIRE[7]; // @[CSR.scala 1156:47]
  wire  f = wdata[5]; // @[CSR.scala 1186:20]
  wire [31:0] _reg_misa_T = ~wdata; // @[CSR.scala 1190:25]
  wire  _reg_misa_T_1 = ~f; // @[CSR.scala 1190:35]
  wire [3:0] _reg_misa_T_2 = {_reg_misa_T_1, 3'h0}; // @[CSR.scala 1190:38]
  wire [31:0] _GEN_611 = {{28'd0}, _reg_misa_T_2}; // @[CSR.scala 1190:32]
  wire [31:0] _reg_misa_T_3 = _reg_misa_T | _GEN_611; // @[CSR.scala 1190:32]
  wire [31:0] _reg_misa_T_4 = ~_reg_misa_T_3; // @[CSR.scala 1190:23]
  wire [31:0] _reg_misa_T_5 = _reg_misa_T_4 & 32'h1005; // @[CSR.scala 1190:55]
  wire [31:0] _reg_misa_T_7 = reg_misa & 32'hffffeffa; // @[CSR.scala 1190:73]
  wire [31:0] _reg_misa_T_8 = _reg_misa_T_5 | _reg_misa_T_7; // @[CSR.scala 1190:62]
  wire [31:0] _reg_mie_T = wdata & 32'h888; // @[CSR.scala 1208:59]
  wire [31:0] _reg_mepc_T_1 = _reg_misa_T | 32'h1; // @[CSR.scala 1564:31]
  wire [31:0] _reg_mepc_T_2 = ~_reg_mepc_T_1; // @[CSR.scala 1564:26]
  wire [31:0] _reg_mcause_T = wdata & 32'h8000000f; // @[CSR.scala 1213:62]
  wire [31:0] _reg_mcountinhibit_T_1 = wdata & 32'hfffffffd; // @[CSR.scala 1233:76]
  wire [31:0] _GEN_295 = decoded_17 ? _reg_mcountinhibit_T_1 : {{29'd0}, reg_mcountinhibit}; // @[CSR.scala 1233:{47,67} 548:34]
  wire [63:0] _T_2000 = {value_1[63:32],wdata}; // @[Cat.scala 31:58]
  wire [63:0] _GEN_296 = decoded_18 ? _T_2000 : {{57'd0}, _GEN_2}; // @[CSR.scala 1558:31 Counters.scala 65:11]
  wire [63:0] _T_2003 = {wdata,value_1[31:0]}; // @[Cat.scala 31:58]
  wire [63:0] _GEN_298 = decoded_107 ? _T_2003 : _GEN_296; // @[CSR.scala 1559:31 Counters.scala 65:11]
  wire [63:0] _T_2005 = {value[63:32],wdata}; // @[Cat.scala 31:58]
  wire [63:0] _GEN_300 = decoded_19 ? _T_2005 : {{57'd0}, _GEN_0}; // @[CSR.scala 1558:31 Counters.scala 65:11]
  wire [63:0] _T_2008 = {wdata,value[31:0]}; // @[Cat.scala 31:58]
  wire [63:0] _GEN_302 = decoded_108 ? _T_2008 : _GEN_300; // @[CSR.scala 1559:31 Counters.scala 65:11]
  wire  new_dcsr_ebreakm = wdata[15]; // @[CSR.scala 1249:43]
  wire [31:0] _newBPC_T_2 = io_rw_cmd[1] ? _T_16 : 32'h0; // @[CSR.scala 1543:9]
  wire [31:0] _newBPC_T_3 = _newBPC_T_2 | io_rw_wdata; // @[CSR.scala 1543:34]
  wire [31:0] _newBPC_T_8 = _newBPC_T_3 & _wdata_T_6; // @[CSR.scala 1543:43]
  wire  newBPC_action = _newBPC_T_8[12]; // @[CSR.scala 1397:96]
  wire  newBPC_dmode = _newBPC_T_8[27]; // @[CSR.scala 1397:96]
  wire  dMode = newBPC_dmode & reg_debug; // @[CSR.scala 1398:38]
  wire  _GEN_310 = dMode & newBPC_action; // @[CSR.scala 1400:{120,51,71}]
  wire  newCfg_r = wdata[0]; // @[CSR.scala 1411:46]
  wire  newCfg_w = wdata[1]; // @[CSR.scala 1411:46]
  wire  newCfg_x = wdata[2]; // @[CSR.scala 1411:46]
  wire [1:0] newCfg_a = wdata[4:3]; // @[CSR.scala 1411:46]
  wire  newCfg_l = wdata[7]; // @[CSR.scala 1411:46]
  wire  _T_2026 = ~reg_pmp_1_cfg_a[1] & reg_pmp_1_cfg_a[0]; // @[PMP.scala 47:20]
  wire  _T_2028 = reg_pmp_0_cfg_l | reg_pmp_1_cfg_l & _T_2026; // @[PMP.scala 49:44]
  wire [31:0] _GEN_381 = decoded_113 & ~_T_2028 ? wdata : {{2'd0}, reg_pmp_0_addr}; // @[CSR.scala 1419:71 1420:18 461:20]
  wire  newCfg_1_r = wdata[8]; // @[CSR.scala 1411:46]
  wire  newCfg_1_w = wdata[9]; // @[CSR.scala 1411:46]
  wire  newCfg_1_x = wdata[10]; // @[CSR.scala 1411:46]
  wire [1:0] newCfg_1_a = wdata[12:11]; // @[CSR.scala 1411:46]
  wire  newCfg_1_l = wdata[15]; // @[CSR.scala 1411:46]
  wire  _T_2036 = ~reg_pmp_2_cfg_a[1] & reg_pmp_2_cfg_a[0]; // @[PMP.scala 47:20]
  wire  _T_2038 = reg_pmp_1_cfg_l | reg_pmp_2_cfg_l & _T_2036; // @[PMP.scala 49:44]
  wire [31:0] _GEN_388 = decoded_114 & ~_T_2038 ? wdata : {{2'd0}, reg_pmp_1_addr}; // @[CSR.scala 1419:71 1420:18 461:20]
  wire  newCfg_2_r = wdata[16]; // @[CSR.scala 1411:46]
  wire  newCfg_2_w = wdata[17]; // @[CSR.scala 1411:46]
  wire  newCfg_2_x = wdata[18]; // @[CSR.scala 1411:46]
  wire [1:0] newCfg_2_a = wdata[20:19]; // @[CSR.scala 1411:46]
  wire  newCfg_2_l = wdata[23]; // @[CSR.scala 1411:46]
  wire  _T_2046 = ~reg_pmp_3_cfg_a[1] & reg_pmp_3_cfg_a[0]; // @[PMP.scala 47:20]
  wire  _T_2048 = reg_pmp_2_cfg_l | reg_pmp_3_cfg_l & _T_2046; // @[PMP.scala 49:44]
  wire [31:0] _GEN_395 = decoded_115 & ~_T_2048 ? wdata : {{2'd0}, reg_pmp_2_addr}; // @[CSR.scala 1419:71 1420:18 461:20]
  wire  newCfg_3_r = wdata[24]; // @[CSR.scala 1411:46]
  wire  newCfg_3_w = wdata[25]; // @[CSR.scala 1411:46]
  wire  newCfg_3_x = wdata[26]; // @[CSR.scala 1411:46]
  wire [1:0] newCfg_3_a = wdata[28:27]; // @[CSR.scala 1411:46]
  wire  newCfg_3_l = wdata[31]; // @[CSR.scala 1411:46]
  wire  _T_2056 = ~reg_pmp_4_cfg_a[1] & reg_pmp_4_cfg_a[0]; // @[PMP.scala 47:20]
  wire  _T_2058 = reg_pmp_3_cfg_l | reg_pmp_4_cfg_l & _T_2056; // @[PMP.scala 49:44]
  wire [31:0] _GEN_402 = decoded_116 & ~_T_2058 ? wdata : {{2'd0}, reg_pmp_3_addr}; // @[CSR.scala 1419:71 1420:18 461:20]
  wire  _T_2066 = ~reg_pmp_5_cfg_a[1] & reg_pmp_5_cfg_a[0]; // @[PMP.scala 47:20]
  wire  _T_2068 = reg_pmp_4_cfg_l | reg_pmp_5_cfg_l & _T_2066; // @[PMP.scala 49:44]
  wire [31:0] _GEN_409 = decoded_117 & ~_T_2068 ? wdata : {{2'd0}, reg_pmp_4_addr}; // @[CSR.scala 1419:71 1420:18 461:20]
  wire  _T_2076 = ~reg_pmp_6_cfg_a[1] & reg_pmp_6_cfg_a[0]; // @[PMP.scala 47:20]
  wire  _T_2078 = reg_pmp_5_cfg_l | reg_pmp_6_cfg_l & _T_2076; // @[PMP.scala 49:44]
  wire [31:0] _GEN_416 = decoded_118 & ~_T_2078 ? wdata : {{2'd0}, reg_pmp_5_addr}; // @[CSR.scala 1419:71 1420:18 461:20]
  wire  _T_2086 = ~reg_pmp_7_cfg_a[1] & reg_pmp_7_cfg_a[0]; // @[PMP.scala 47:20]
  wire  _T_2088 = reg_pmp_6_cfg_l | reg_pmp_7_cfg_l & _T_2086; // @[PMP.scala 49:44]
  wire [31:0] _GEN_423 = decoded_119 & ~_T_2088 ? wdata : {{2'd0}, reg_pmp_6_addr}; // @[CSR.scala 1419:71 1420:18 461:20]
  wire  _T_2098 = reg_pmp_7_cfg_l | reg_pmp_7_cfg_l & _T_2086; // @[PMP.scala 49:44]
  wire [31:0] _GEN_430 = decoded_120 & ~_T_2098 ? wdata : {{2'd0}, reg_pmp_7_addr}; // @[CSR.scala 1419:71 1420:18 461:20]
  wire [31:0] _reg_custom_0_T = wdata & 32'h8; // @[CSR.scala 1426:23]
  wire [31:0] _reg_custom_0_T_2 = reg_custom_0 & 32'hfffffff7; // @[CSR.scala 1426:38]
  wire [31:0] _reg_custom_0_T_3 = _reg_custom_0_T | _reg_custom_0_T_2; // @[CSR.scala 1426:31]
  wire [31:0] _GEN_449 = csr_wen ? _GEN_295 : {{29'd0}, reg_mcountinhibit}; // @[CSR.scala 1151:18 548:34]
  wire [63:0] _GEN_450 = csr_wen ? _GEN_298 : {{57'd0}, _GEN_2}; // @[CSR.scala 1151:18]
  wire [63:0] _GEN_452 = csr_wen ? _GEN_302 : {{57'd0}, _GEN_0}; // @[CSR.scala 1151:18]
  wire [31:0] _GEN_497 = csr_wen ? _GEN_381 : {{2'd0}, reg_pmp_0_addr}; // @[CSR.scala 1151:18 461:20]
  wire [31:0] _GEN_504 = csr_wen ? _GEN_388 : {{2'd0}, reg_pmp_1_addr}; // @[CSR.scala 1151:18 461:20]
  wire [31:0] _GEN_511 = csr_wen ? _GEN_395 : {{2'd0}, reg_pmp_2_addr}; // @[CSR.scala 1151:18 461:20]
  wire [31:0] _GEN_518 = csr_wen ? _GEN_402 : {{2'd0}, reg_pmp_3_addr}; // @[CSR.scala 1151:18 461:20]
  wire [31:0] _GEN_525 = csr_wen ? _GEN_409 : {{2'd0}, reg_pmp_4_addr}; // @[CSR.scala 1151:18 461:20]
  wire [31:0] _GEN_532 = csr_wen ? _GEN_416 : {{2'd0}, reg_pmp_5_addr}; // @[CSR.scala 1151:18 461:20]
  wire [31:0] _GEN_539 = csr_wen ? _GEN_423 : {{2'd0}, reg_pmp_6_addr}; // @[CSR.scala 1151:18 461:20]
  wire [31:0] _GEN_546 = csr_wen ? _GEN_430 : {{2'd0}, reg_pmp_7_addr}; // @[CSR.scala 1151:18 461:20]
  assign io_rw_rdata = _io_rw_rdata_T_264[31:0]; // @[CSR.scala 1104:15]
  assign io_decode_0_fp_illegal = io_status_fs == 2'h0 | ~reg_misa[5]; // @[CSR.scala 853:87]
  assign io_decode_0_fp_csr = 1'h0; // @[Decode.scala 55:116]
  assign io_decode_0_rocc_illegal = io_status_xs == 2'h0 | ~reg_misa[23]; // @[CSR.scala 856:89]
  assign io_decode_0_read_illegal = _io_decode_0_read_illegal_T_17 | _io_decode_0_read_illegal_T_21; // @[CSR.scala 865:68]
  assign io_decode_0_write_illegal = &addr_1[11:10]; // @[CSR.scala 867:41]
  assign io_decode_0_write_flush = ~(io_decode_0_write_flush_addr_m >= 12'h340 & io_decode_0_write_flush_addr_m <= 12'h343
    ); // @[CSR.scala 870:7]
  assign io_decode_0_system_illegal = is_ret & io_decode_0_read_illegal_andMatrixInput_6 &
    io_decode_0_read_illegal_andMatrixInput_3 & _io_decode_0_read_illegal_T_15; // @[CSR.scala 875:37]
  assign io_csr_stall = reg_wfi | io_status_cease; // @[CSR.scala 1094:27]
  assign io_eret = insn_call | insn_break | insn_ret; // @[CSR.scala 936:38]
  assign io_singleStep = reg_dcsr_step & _io_decode_0_read_illegal_T_15; // @[CSR.scala 937:34]
  assign io_status_debug = reg_debug; // @[CSR.scala 940:19]
  assign io_status_cease = io_status_cease_r; // @[CSR.scala 1095:19]
  assign io_status_wfi = reg_wfi; // @[CSR.scala 1096:17]
  assign io_status_isa = reg_misa; // @[CSR.scala 941:17]
  assign io_status_dprv = 2'h3; // @[CSR.scala 944:24]
  assign io_status_dv = 1'h0; // @[CSR.scala 945:33]
  assign io_status_prv = 2'h3; // @[CSR.scala 938:13]
  assign io_status_v = 1'h0; // @[CSR.scala 938:13]
  assign io_status_sd = &io_status_fs | &io_status_xs | &io_status_vs; // @[CSR.scala 939:58]
  assign io_status_zero2 = 23'h0; // @[CSR.scala 938:13]
  assign io_status_mpv = 1'h0; // @[CSR.scala 947:17]
  assign io_status_gva = reg_mstatus_gva; // @[CSR.scala 948:17]
  assign io_status_mbe = 1'h0; // @[CSR.scala 938:13]
  assign io_status_sbe = 1'h0; // @[CSR.scala 938:13]
  assign io_status_sxl = 2'h0; // @[CSR.scala 943:17]
  assign io_status_uxl = 2'h0; // @[CSR.scala 942:17]
  assign io_status_sd_rv32 = io_status_sd; // @[CSR.scala 946:35]
  assign io_status_zero1 = 8'h0; // @[CSR.scala 938:13]
  assign io_status_tsr = 1'h0; // @[CSR.scala 938:13]
  assign io_status_tw = 1'h0; // @[CSR.scala 938:13]
  assign io_status_tvm = 1'h0; // @[CSR.scala 938:13]
  assign io_status_mxr = 1'h0; // @[CSR.scala 938:13]
  assign io_status_sum = 1'h0; // @[CSR.scala 938:13]
  assign io_status_mprv = 1'h0; // @[CSR.scala 938:13]
  assign io_status_xs = 2'h0; // @[CSR.scala 938:13]
  assign io_status_fs = 2'h0; // @[CSR.scala 938:13]
  assign io_status_mpp = 2'h3; // @[CSR.scala 938:13]
  assign io_status_vs = 2'h0; // @[CSR.scala 938:13]
  assign io_status_spp = reg_mstatus_spp; // @[CSR.scala 938:13]
  assign io_status_mpie = reg_mstatus_mpie; // @[CSR.scala 938:13]
  assign io_status_ube = 1'h0; // @[CSR.scala 938:13]
  assign io_status_spie = 1'h0; // @[CSR.scala 938:13]
  assign io_status_upie = 1'h0; // @[CSR.scala 938:13]
  assign io_status_mie = reg_mstatus_mie; // @[CSR.scala 938:13]
  assign io_status_hie = 1'h0; // @[CSR.scala 938:13]
  assign io_status_sie = 1'h0; // @[CSR.scala 938:13]
  assign io_status_uie = 1'h0; // @[CSR.scala 938:13]
  assign io_evec = insn_ret ? _GEN_239 : tvec; // @[CSR.scala 1048:19 932:11]
  assign io_time = value_1[31:0]; // @[CSR.scala 1093:11]
  assign io_interrupt = (anyInterrupt & ~io_singleStep | reg_singleStepped) & ~(reg_debug | io_status_cease); // @[CSR.scala 584:73]
  assign io_interrupt_cause = 32'h80000000 + _GEN_41; // @[CSR.scala 583:67]
  assign io_bp_0_control_action = reg_bp_0_control_action; // @[CSR.scala 586:9]
  assign io_bp_0_control_tmatch = reg_bp_0_control_tmatch; // @[CSR.scala 586:9]
  assign io_bp_0_control_x = reg_bp_0_control_x; // @[CSR.scala 586:9]
  assign io_bp_0_control_w = reg_bp_0_control_w; // @[CSR.scala 586:9]
  assign io_bp_0_control_r = reg_bp_0_control_r; // @[CSR.scala 586:9]
  assign io_bp_0_address = reg_bp_0_address; // @[CSR.scala 586:9]
  assign io_pmp_0_cfg_l = reg_pmp_0_cfg_l; // @[PMP.scala 24:19 25:13]
  assign io_pmp_0_cfg_a = reg_pmp_0_cfg_a; // @[PMP.scala 24:19 25:13]
  assign io_pmp_0_cfg_x = reg_pmp_0_cfg_x; // @[PMP.scala 24:19 25:13]
  assign io_pmp_0_cfg_w = reg_pmp_0_cfg_w; // @[PMP.scala 24:19 25:13]
  assign io_pmp_0_cfg_r = reg_pmp_0_cfg_r; // @[PMP.scala 24:19 25:13]
  assign io_pmp_0_addr = reg_pmp_0_addr; // @[PMP.scala 24:19 26:14]
  assign io_pmp_0_mask = _pmp_mask_T_4[31:0]; // @[PMP.scala 24:19 27:14]
  assign io_pmp_1_cfg_l = reg_pmp_1_cfg_l; // @[PMP.scala 24:19 25:13]
  assign io_pmp_1_cfg_a = reg_pmp_1_cfg_a; // @[PMP.scala 24:19 25:13]
  assign io_pmp_1_cfg_x = reg_pmp_1_cfg_x; // @[PMP.scala 24:19 25:13]
  assign io_pmp_1_cfg_w = reg_pmp_1_cfg_w; // @[PMP.scala 24:19 25:13]
  assign io_pmp_1_cfg_r = reg_pmp_1_cfg_r; // @[PMP.scala 24:19 25:13]
  assign io_pmp_1_addr = reg_pmp_1_addr; // @[PMP.scala 24:19 26:14]
  assign io_pmp_1_mask = _pmp_mask_T_9[31:0]; // @[PMP.scala 24:19 27:14]
  assign io_pmp_2_cfg_l = reg_pmp_2_cfg_l; // @[PMP.scala 24:19 25:13]
  assign io_pmp_2_cfg_a = reg_pmp_2_cfg_a; // @[PMP.scala 24:19 25:13]
  assign io_pmp_2_cfg_x = reg_pmp_2_cfg_x; // @[PMP.scala 24:19 25:13]
  assign io_pmp_2_cfg_w = reg_pmp_2_cfg_w; // @[PMP.scala 24:19 25:13]
  assign io_pmp_2_cfg_r = reg_pmp_2_cfg_r; // @[PMP.scala 24:19 25:13]
  assign io_pmp_2_addr = reg_pmp_2_addr; // @[PMP.scala 24:19 26:14]
  assign io_pmp_2_mask = _pmp_mask_T_14[31:0]; // @[PMP.scala 24:19 27:14]
  assign io_pmp_3_cfg_l = reg_pmp_3_cfg_l; // @[PMP.scala 24:19 25:13]
  assign io_pmp_3_cfg_a = reg_pmp_3_cfg_a; // @[PMP.scala 24:19 25:13]
  assign io_pmp_3_cfg_x = reg_pmp_3_cfg_x; // @[PMP.scala 24:19 25:13]
  assign io_pmp_3_cfg_w = reg_pmp_3_cfg_w; // @[PMP.scala 24:19 25:13]
  assign io_pmp_3_cfg_r = reg_pmp_3_cfg_r; // @[PMP.scala 24:19 25:13]
  assign io_pmp_3_addr = reg_pmp_3_addr; // @[PMP.scala 24:19 26:14]
  assign io_pmp_3_mask = _pmp_mask_T_19[31:0]; // @[PMP.scala 24:19 27:14]
  assign io_pmp_4_cfg_l = reg_pmp_4_cfg_l; // @[PMP.scala 24:19 25:13]
  assign io_pmp_4_cfg_a = reg_pmp_4_cfg_a; // @[PMP.scala 24:19 25:13]
  assign io_pmp_4_cfg_x = reg_pmp_4_cfg_x; // @[PMP.scala 24:19 25:13]
  assign io_pmp_4_cfg_w = reg_pmp_4_cfg_w; // @[PMP.scala 24:19 25:13]
  assign io_pmp_4_cfg_r = reg_pmp_4_cfg_r; // @[PMP.scala 24:19 25:13]
  assign io_pmp_4_addr = reg_pmp_4_addr; // @[PMP.scala 24:19 26:14]
  assign io_pmp_4_mask = _pmp_mask_T_24[31:0]; // @[PMP.scala 24:19 27:14]
  assign io_pmp_5_cfg_l = reg_pmp_5_cfg_l; // @[PMP.scala 24:19 25:13]
  assign io_pmp_5_cfg_a = reg_pmp_5_cfg_a; // @[PMP.scala 24:19 25:13]
  assign io_pmp_5_cfg_x = reg_pmp_5_cfg_x; // @[PMP.scala 24:19 25:13]
  assign io_pmp_5_cfg_w = reg_pmp_5_cfg_w; // @[PMP.scala 24:19 25:13]
  assign io_pmp_5_cfg_r = reg_pmp_5_cfg_r; // @[PMP.scala 24:19 25:13]
  assign io_pmp_5_addr = reg_pmp_5_addr; // @[PMP.scala 24:19 26:14]
  assign io_pmp_5_mask = _pmp_mask_T_29[31:0]; // @[PMP.scala 24:19 27:14]
  assign io_pmp_6_cfg_l = reg_pmp_6_cfg_l; // @[PMP.scala 24:19 25:13]
  assign io_pmp_6_cfg_a = reg_pmp_6_cfg_a; // @[PMP.scala 24:19 25:13]
  assign io_pmp_6_cfg_x = reg_pmp_6_cfg_x; // @[PMP.scala 24:19 25:13]
  assign io_pmp_6_cfg_w = reg_pmp_6_cfg_w; // @[PMP.scala 24:19 25:13]
  assign io_pmp_6_cfg_r = reg_pmp_6_cfg_r; // @[PMP.scala 24:19 25:13]
  assign io_pmp_6_addr = reg_pmp_6_addr; // @[PMP.scala 24:19 26:14]
  assign io_pmp_6_mask = _pmp_mask_T_34[31:0]; // @[PMP.scala 24:19 27:14]
  assign io_pmp_7_cfg_l = reg_pmp_7_cfg_l; // @[PMP.scala 24:19 25:13]
  assign io_pmp_7_cfg_a = reg_pmp_7_cfg_a; // @[PMP.scala 24:19 25:13]
  assign io_pmp_7_cfg_x = reg_pmp_7_cfg_x; // @[PMP.scala 24:19 25:13]
  assign io_pmp_7_cfg_w = reg_pmp_7_cfg_w; // @[PMP.scala 24:19 25:13]
  assign io_pmp_7_cfg_r = reg_pmp_7_cfg_r; // @[PMP.scala 24:19 25:13]
  assign io_pmp_7_addr = reg_pmp_7_addr; // @[PMP.scala 24:19 26:14]
  assign io_pmp_7_mask = _pmp_mask_T_39[31:0]; // @[PMP.scala 24:19 27:14]
  assign io_inhibit_cycle = reg_mcountinhibit[0]; // @[CSR.scala 549:40]
  assign io_trace_0_valid = io_retire > 1'h0 | io_trace_0_exception; // @[CSR.scala 1522:30]
  assign io_trace_0_iaddr = io_pc; // @[CSR.scala 1524:13]
  assign io_trace_0_insn = io_inst_0; // @[CSR.scala 1523:12]
  assign io_trace_0_exception = _io_eret_T | io_exception; // @[CSR.scala 956:43]
  assign io_customCSRs_0_value = reg_custom_0; // @[CSR.scala 1101:14]
  always @(posedge clock) begin
    if (reset) begin // @[CSR.scala 370:24]
      reg_mstatus_gva <= 1'h0; // @[CSR.scala 370:24]
    end else if (exception) begin // @[CSR.scala 970:20]
      if (!(trapToDebug)) begin // @[CSR.scala 971:24]
        reg_mstatus_gva <= io_gva;
      end
    end
    if (reset) begin // @[CSR.scala 370:24]
      reg_mstatus_spp <= 1'h0; // @[CSR.scala 370:24]
    end else begin
      reg_mstatus_spp <= _GEN_207[0];
    end
    if (reset) begin // @[CSR.scala 370:24]
      reg_mstatus_mpie <= 1'h0; // @[CSR.scala 370:24]
    end else if (csr_wen) begin // @[CSR.scala 1151:18]
      if (decoded_5) begin // @[CSR.scala 1155:39]
        reg_mstatus_mpie <= new_mstatus_mpie; // @[CSR.scala 1158:24]
      end else begin
        reg_mstatus_mpie <= _GEN_274;
      end
    end else begin
      reg_mstatus_mpie <= _GEN_274;
    end
    if (reset) begin // @[CSR.scala 370:24]
      reg_mstatus_mie <= 1'h0; // @[CSR.scala 370:24]
    end else if (csr_wen) begin // @[CSR.scala 1151:18]
      if (decoded_5) begin // @[CSR.scala 1155:39]
        reg_mstatus_mie <= new_mstatus_mie; // @[CSR.scala 1157:23]
      end else begin
        reg_mstatus_mie <= _GEN_273;
      end
    end else begin
      reg_mstatus_mie <= _GEN_273;
    end
    if (reset) begin // @[CSR.scala 378:21]
      reg_dcsr_ebreakm <= 1'h0; // @[CSR.scala 378:21]
    end else if (csr_wen) begin // @[CSR.scala 1151:18]
      if (decoded_14) begin // @[CSR.scala 1248:38]
        reg_dcsr_ebreakm <= new_dcsr_ebreakm; // @[CSR.scala 1251:26]
      end
    end
    if (reset) begin // @[CSR.scala 378:21]
      reg_dcsr_cause <= 3'h0; // @[CSR.scala 378:21]
    end else if (exception) begin // @[CSR.scala 970:20]
      if (trapToDebug) begin // @[CSR.scala 971:24]
        if (_io_decode_0_read_illegal_T_15) begin // @[CSR.scala 972:25]
          reg_dcsr_cause <= _reg_dcsr_cause_T_2; // @[CSR.scala 976:24]
        end
      end
    end
    if (reset) begin // @[CSR.scala 378:21]
      reg_dcsr_step <= 1'h0; // @[CSR.scala 378:21]
    end else if (csr_wen) begin // @[CSR.scala 1151:18]
      if (decoded_14) begin // @[CSR.scala 1248:38]
        reg_dcsr_step <= wdata[2]; // @[CSR.scala 1250:23]
      end
    end
    if (reset) begin // @[CSR.scala 450:22]
      reg_debug <= 1'h0; // @[CSR.scala 450:22]
    end else if (insn_ret) begin // @[CSR.scala 1048:19]
      if (io_rw_addr[10] & io_rw_addr[7]) begin // @[CSR.scala 1067:70]
        reg_debug <= 1'h0; // @[CSR.scala 1070:17]
      end else begin
        reg_debug <= _GEN_182;
      end
    end else begin
      reg_debug <= _GEN_182;
    end
    if (csr_wen) begin // @[CSR.scala 1151:18]
      if (decoded_15) begin // @[CSR.scala 1257:42]
        reg_dpc <= _reg_mepc_T_2; // @[CSR.scala 1257:52]
      end else begin
        reg_dpc <= _GEN_183;
      end
    end else begin
      reg_dpc <= _GEN_183;
    end
    if (csr_wen) begin // @[CSR.scala 1151:18]
      if (decoded_16) begin // @[CSR.scala 1258:43]
        reg_dscratch0 <= wdata; // @[CSR.scala 1258:59]
      end
    end
    if (_io_interrupt_T) begin // @[CSR.scala 964:25]
      reg_singleStepped <= 1'h0; // @[CSR.scala 964:45]
    end else begin
      reg_singleStepped <= _GEN_48;
    end
    if (reset) begin // @[CSR.scala 1500:18]
      reg_bp_0_control_dmode <= 1'h0; // @[CSR.scala 1502:17]
    end else if (csr_wen) begin // @[CSR.scala 1151:18]
      if (~reg_bp_0_control_dmode | reg_debug) begin // @[CSR.scala 1378:70]
        if (decoded_1) begin // @[CSR.scala 1390:44]
          reg_bp_0_control_dmode <= dMode; // @[CSR.scala 1399:30]
        end
      end
    end
    if (reset) begin // @[CSR.scala 1500:18]
      reg_bp_0_control_action <= 1'h0; // @[CSR.scala 1501:18]
    end else if (csr_wen) begin // @[CSR.scala 1151:18]
      if (~reg_bp_0_control_dmode | reg_debug) begin // @[CSR.scala 1378:70]
        if (decoded_1) begin // @[CSR.scala 1390:44]
          reg_bp_0_control_action <= _GEN_310;
        end
      end
    end
    if (csr_wen) begin // @[CSR.scala 1151:18]
      if (~reg_bp_0_control_dmode | reg_debug) begin // @[CSR.scala 1378:70]
        if (decoded_1) begin // @[CSR.scala 1390:44]
          reg_bp_0_control_tmatch <= wdata[8:7]; // @[CSR.scala 1391:24]
        end
      end
    end
    if (reset) begin // @[CSR.scala 1500:18]
      reg_bp_0_control_x <= 1'h0; // @[CSR.scala 1506:13]
    end else if (csr_wen) begin // @[CSR.scala 1151:18]
      if (~reg_bp_0_control_dmode | reg_debug) begin // @[CSR.scala 1378:70]
        if (decoded_1) begin // @[CSR.scala 1390:44]
          reg_bp_0_control_x <= wdata[2]; // @[CSR.scala 1391:24]
        end
      end
    end
    if (reset) begin // @[CSR.scala 1500:18]
      reg_bp_0_control_w <= 1'h0; // @[CSR.scala 1505:13]
    end else if (csr_wen) begin // @[CSR.scala 1151:18]
      if (~reg_bp_0_control_dmode | reg_debug) begin // @[CSR.scala 1378:70]
        if (decoded_1) begin // @[CSR.scala 1390:44]
          reg_bp_0_control_w <= wdata[1]; // @[CSR.scala 1391:24]
        end
      end
    end
    if (reset) begin // @[CSR.scala 1500:18]
      reg_bp_0_control_r <= 1'h0; // @[CSR.scala 1504:13]
    end else if (csr_wen) begin // @[CSR.scala 1151:18]
      if (~reg_bp_0_control_dmode | reg_debug) begin // @[CSR.scala 1378:70]
        if (decoded_1) begin // @[CSR.scala 1390:44]
          reg_bp_0_control_r <= wdata[0]; // @[CSR.scala 1391:24]
        end
      end
    end
    if (csr_wen) begin // @[CSR.scala 1151:18]
      if (~reg_bp_0_control_dmode | reg_debug) begin // @[CSR.scala 1378:70]
        if (decoded_2) begin // @[CSR.scala 1379:44]
          reg_bp_0_address <= wdata; // @[CSR.scala 1379:57]
        end
      end
    end
    if (reset) begin // @[CSR.scala 1517:18]
      reg_pmp_0_cfg_l <= 1'h0; // @[PMP.scala 38:11]
    end else if (csr_wen) begin // @[CSR.scala 1151:18]
      if (decoded_109 & ~reg_pmp_0_cfg_l) begin // @[CSR.scala 1410:76]
        reg_pmp_0_cfg_l <= newCfg_l; // @[CSR.scala 1412:17]
      end
    end
    if (reset) begin // @[CSR.scala 1517:18]
      reg_pmp_0_cfg_a <= 2'h0; // @[PMP.scala 37:11]
    end else if (csr_wen) begin // @[CSR.scala 1151:18]
      if (decoded_109 & ~reg_pmp_0_cfg_l) begin // @[CSR.scala 1410:76]
        reg_pmp_0_cfg_a <= newCfg_a; // @[CSR.scala 1412:17]
      end
    end
    if (csr_wen) begin // @[CSR.scala 1151:18]
      if (decoded_109 & ~reg_pmp_0_cfg_l) begin // @[CSR.scala 1410:76]
        reg_pmp_0_cfg_x <= newCfg_x; // @[CSR.scala 1412:17]
      end
    end
    if (csr_wen) begin // @[CSR.scala 1151:18]
      if (decoded_109 & ~reg_pmp_0_cfg_l) begin // @[CSR.scala 1410:76]
        reg_pmp_0_cfg_w <= newCfg_w & newCfg_r; // @[CSR.scala 1414:19]
      end
    end
    if (csr_wen) begin // @[CSR.scala 1151:18]
      if (decoded_109 & ~reg_pmp_0_cfg_l) begin // @[CSR.scala 1410:76]
        reg_pmp_0_cfg_r <= newCfg_r; // @[CSR.scala 1412:17]
      end
    end
    reg_pmp_0_addr <= _GEN_497[29:0];
    if (reset) begin // @[CSR.scala 1517:18]
      reg_pmp_1_cfg_l <= 1'h0; // @[PMP.scala 38:11]
    end else if (csr_wen) begin // @[CSR.scala 1151:18]
      if (decoded_109 & ~reg_pmp_1_cfg_l) begin // @[CSR.scala 1410:76]
        reg_pmp_1_cfg_l <= newCfg_1_l; // @[CSR.scala 1412:17]
      end
    end
    if (reset) begin // @[CSR.scala 1517:18]
      reg_pmp_1_cfg_a <= 2'h0; // @[PMP.scala 37:11]
    end else if (csr_wen) begin // @[CSR.scala 1151:18]
      if (decoded_109 & ~reg_pmp_1_cfg_l) begin // @[CSR.scala 1410:76]
        reg_pmp_1_cfg_a <= newCfg_1_a; // @[CSR.scala 1412:17]
      end
    end
    if (csr_wen) begin // @[CSR.scala 1151:18]
      if (decoded_109 & ~reg_pmp_1_cfg_l) begin // @[CSR.scala 1410:76]
        reg_pmp_1_cfg_x <= newCfg_1_x; // @[CSR.scala 1412:17]
      end
    end
    if (csr_wen) begin // @[CSR.scala 1151:18]
      if (decoded_109 & ~reg_pmp_1_cfg_l) begin // @[CSR.scala 1410:76]
        reg_pmp_1_cfg_w <= newCfg_1_w & newCfg_1_r; // @[CSR.scala 1414:19]
      end
    end
    if (csr_wen) begin // @[CSR.scala 1151:18]
      if (decoded_109 & ~reg_pmp_1_cfg_l) begin // @[CSR.scala 1410:76]
        reg_pmp_1_cfg_r <= newCfg_1_r; // @[CSR.scala 1412:17]
      end
    end
    reg_pmp_1_addr <= _GEN_504[29:0];
    if (reset) begin // @[CSR.scala 1517:18]
      reg_pmp_2_cfg_l <= 1'h0; // @[PMP.scala 38:11]
    end else if (csr_wen) begin // @[CSR.scala 1151:18]
      if (decoded_109 & ~reg_pmp_2_cfg_l) begin // @[CSR.scala 1410:76]
        reg_pmp_2_cfg_l <= newCfg_2_l; // @[CSR.scala 1412:17]
      end
    end
    if (reset) begin // @[CSR.scala 1517:18]
      reg_pmp_2_cfg_a <= 2'h0; // @[PMP.scala 37:11]
    end else if (csr_wen) begin // @[CSR.scala 1151:18]
      if (decoded_109 & ~reg_pmp_2_cfg_l) begin // @[CSR.scala 1410:76]
        reg_pmp_2_cfg_a <= newCfg_2_a; // @[CSR.scala 1412:17]
      end
    end
    if (csr_wen) begin // @[CSR.scala 1151:18]
      if (decoded_109 & ~reg_pmp_2_cfg_l) begin // @[CSR.scala 1410:76]
        reg_pmp_2_cfg_x <= newCfg_2_x; // @[CSR.scala 1412:17]
      end
    end
    if (csr_wen) begin // @[CSR.scala 1151:18]
      if (decoded_109 & ~reg_pmp_2_cfg_l) begin // @[CSR.scala 1410:76]
        reg_pmp_2_cfg_w <= newCfg_2_w & newCfg_2_r; // @[CSR.scala 1414:19]
      end
    end
    if (csr_wen) begin // @[CSR.scala 1151:18]
      if (decoded_109 & ~reg_pmp_2_cfg_l) begin // @[CSR.scala 1410:76]
        reg_pmp_2_cfg_r <= newCfg_2_r; // @[CSR.scala 1412:17]
      end
    end
    reg_pmp_2_addr <= _GEN_511[29:0];
    if (reset) begin // @[CSR.scala 1517:18]
      reg_pmp_3_cfg_l <= 1'h0; // @[PMP.scala 38:11]
    end else if (csr_wen) begin // @[CSR.scala 1151:18]
      if (decoded_109 & ~reg_pmp_3_cfg_l) begin // @[CSR.scala 1410:76]
        reg_pmp_3_cfg_l <= newCfg_3_l; // @[CSR.scala 1412:17]
      end
    end
    if (reset) begin // @[CSR.scala 1517:18]
      reg_pmp_3_cfg_a <= 2'h0; // @[PMP.scala 37:11]
    end else if (csr_wen) begin // @[CSR.scala 1151:18]
      if (decoded_109 & ~reg_pmp_3_cfg_l) begin // @[CSR.scala 1410:76]
        reg_pmp_3_cfg_a <= newCfg_3_a; // @[CSR.scala 1412:17]
      end
    end
    if (csr_wen) begin // @[CSR.scala 1151:18]
      if (decoded_109 & ~reg_pmp_3_cfg_l) begin // @[CSR.scala 1410:76]
        reg_pmp_3_cfg_x <= newCfg_3_x; // @[CSR.scala 1412:17]
      end
    end
    if (csr_wen) begin // @[CSR.scala 1151:18]
      if (decoded_109 & ~reg_pmp_3_cfg_l) begin // @[CSR.scala 1410:76]
        reg_pmp_3_cfg_w <= newCfg_3_w & newCfg_3_r; // @[CSR.scala 1414:19]
      end
    end
    if (csr_wen) begin // @[CSR.scala 1151:18]
      if (decoded_109 & ~reg_pmp_3_cfg_l) begin // @[CSR.scala 1410:76]
        reg_pmp_3_cfg_r <= newCfg_3_r; // @[CSR.scala 1412:17]
      end
    end
    reg_pmp_3_addr <= _GEN_518[29:0];
    if (reset) begin // @[CSR.scala 1517:18]
      reg_pmp_4_cfg_l <= 1'h0; // @[PMP.scala 38:11]
    end else if (csr_wen) begin // @[CSR.scala 1151:18]
      if (decoded_110 & ~reg_pmp_4_cfg_l) begin // @[CSR.scala 1410:76]
        reg_pmp_4_cfg_l <= newCfg_l; // @[CSR.scala 1412:17]
      end
    end
    if (reset) begin // @[CSR.scala 1517:18]
      reg_pmp_4_cfg_a <= 2'h0; // @[PMP.scala 37:11]
    end else if (csr_wen) begin // @[CSR.scala 1151:18]
      if (decoded_110 & ~reg_pmp_4_cfg_l) begin // @[CSR.scala 1410:76]
        reg_pmp_4_cfg_a <= newCfg_a; // @[CSR.scala 1412:17]
      end
    end
    if (csr_wen) begin // @[CSR.scala 1151:18]
      if (decoded_110 & ~reg_pmp_4_cfg_l) begin // @[CSR.scala 1410:76]
        reg_pmp_4_cfg_x <= newCfg_x; // @[CSR.scala 1412:17]
      end
    end
    if (csr_wen) begin // @[CSR.scala 1151:18]
      if (decoded_110 & ~reg_pmp_4_cfg_l) begin // @[CSR.scala 1410:76]
        reg_pmp_4_cfg_w <= newCfg_w & newCfg_r; // @[CSR.scala 1414:19]
      end
    end
    if (csr_wen) begin // @[CSR.scala 1151:18]
      if (decoded_110 & ~reg_pmp_4_cfg_l) begin // @[CSR.scala 1410:76]
        reg_pmp_4_cfg_r <= newCfg_r; // @[CSR.scala 1412:17]
      end
    end
    reg_pmp_4_addr <= _GEN_525[29:0];
    if (reset) begin // @[CSR.scala 1517:18]
      reg_pmp_5_cfg_l <= 1'h0; // @[PMP.scala 38:11]
    end else if (csr_wen) begin // @[CSR.scala 1151:18]
      if (decoded_110 & ~reg_pmp_5_cfg_l) begin // @[CSR.scala 1410:76]
        reg_pmp_5_cfg_l <= newCfg_1_l; // @[CSR.scala 1412:17]
      end
    end
    if (reset) begin // @[CSR.scala 1517:18]
      reg_pmp_5_cfg_a <= 2'h0; // @[PMP.scala 37:11]
    end else if (csr_wen) begin // @[CSR.scala 1151:18]
      if (decoded_110 & ~reg_pmp_5_cfg_l) begin // @[CSR.scala 1410:76]
        reg_pmp_5_cfg_a <= newCfg_1_a; // @[CSR.scala 1412:17]
      end
    end
    if (csr_wen) begin // @[CSR.scala 1151:18]
      if (decoded_110 & ~reg_pmp_5_cfg_l) begin // @[CSR.scala 1410:76]
        reg_pmp_5_cfg_x <= newCfg_1_x; // @[CSR.scala 1412:17]
      end
    end
    if (csr_wen) begin // @[CSR.scala 1151:18]
      if (decoded_110 & ~reg_pmp_5_cfg_l) begin // @[CSR.scala 1410:76]
        reg_pmp_5_cfg_w <= newCfg_1_w & newCfg_1_r; // @[CSR.scala 1414:19]
      end
    end
    if (csr_wen) begin // @[CSR.scala 1151:18]
      if (decoded_110 & ~reg_pmp_5_cfg_l) begin // @[CSR.scala 1410:76]
        reg_pmp_5_cfg_r <= newCfg_1_r; // @[CSR.scala 1412:17]
      end
    end
    reg_pmp_5_addr <= _GEN_532[29:0];
    if (reset) begin // @[CSR.scala 1517:18]
      reg_pmp_6_cfg_l <= 1'h0; // @[PMP.scala 38:11]
    end else if (csr_wen) begin // @[CSR.scala 1151:18]
      if (decoded_110 & ~reg_pmp_6_cfg_l) begin // @[CSR.scala 1410:76]
        reg_pmp_6_cfg_l <= newCfg_2_l; // @[CSR.scala 1412:17]
      end
    end
    if (reset) begin // @[CSR.scala 1517:18]
      reg_pmp_6_cfg_a <= 2'h0; // @[PMP.scala 37:11]
    end else if (csr_wen) begin // @[CSR.scala 1151:18]
      if (decoded_110 & ~reg_pmp_6_cfg_l) begin // @[CSR.scala 1410:76]
        reg_pmp_6_cfg_a <= newCfg_2_a; // @[CSR.scala 1412:17]
      end
    end
    if (csr_wen) begin // @[CSR.scala 1151:18]
      if (decoded_110 & ~reg_pmp_6_cfg_l) begin // @[CSR.scala 1410:76]
        reg_pmp_6_cfg_x <= newCfg_2_x; // @[CSR.scala 1412:17]
      end
    end
    if (csr_wen) begin // @[CSR.scala 1151:18]
      if (decoded_110 & ~reg_pmp_6_cfg_l) begin // @[CSR.scala 1410:76]
        reg_pmp_6_cfg_w <= newCfg_2_w & newCfg_2_r; // @[CSR.scala 1414:19]
      end
    end
    if (csr_wen) begin // @[CSR.scala 1151:18]
      if (decoded_110 & ~reg_pmp_6_cfg_l) begin // @[CSR.scala 1410:76]
        reg_pmp_6_cfg_r <= newCfg_2_r; // @[CSR.scala 1412:17]
      end
    end
    reg_pmp_6_addr <= _GEN_539[29:0];
    if (reset) begin // @[CSR.scala 1517:18]
      reg_pmp_7_cfg_l <= 1'h0; // @[PMP.scala 38:11]
    end else if (csr_wen) begin // @[CSR.scala 1151:18]
      if (decoded_110 & ~reg_pmp_7_cfg_l) begin // @[CSR.scala 1410:76]
        reg_pmp_7_cfg_l <= newCfg_3_l; // @[CSR.scala 1412:17]
      end
    end
    if (reset) begin // @[CSR.scala 1517:18]
      reg_pmp_7_cfg_a <= 2'h0; // @[PMP.scala 37:11]
    end else if (csr_wen) begin // @[CSR.scala 1151:18]
      if (decoded_110 & ~reg_pmp_7_cfg_l) begin // @[CSR.scala 1410:76]
        reg_pmp_7_cfg_a <= newCfg_3_a; // @[CSR.scala 1412:17]
      end
    end
    if (csr_wen) begin // @[CSR.scala 1151:18]
      if (decoded_110 & ~reg_pmp_7_cfg_l) begin // @[CSR.scala 1410:76]
        reg_pmp_7_cfg_x <= newCfg_3_x; // @[CSR.scala 1412:17]
      end
    end
    if (csr_wen) begin // @[CSR.scala 1151:18]
      if (decoded_110 & ~reg_pmp_7_cfg_l) begin // @[CSR.scala 1410:76]
        reg_pmp_7_cfg_w <= newCfg_3_w & newCfg_3_r; // @[CSR.scala 1414:19]
      end
    end
    if (csr_wen) begin // @[CSR.scala 1151:18]
      if (decoded_110 & ~reg_pmp_7_cfg_l) begin // @[CSR.scala 1410:76]
        reg_pmp_7_cfg_r <= newCfg_3_r; // @[CSR.scala 1412:17]
      end
    end
    reg_pmp_7_addr <= _GEN_546[29:0];
    if (csr_wen) begin // @[CSR.scala 1151:18]
      if (decoded_8) begin // @[CSR.scala 1208:40]
        reg_mie <= _reg_mie_T; // @[CSR.scala 1208:50]
      end
    end
    if (csr_wen) begin // @[CSR.scala 1151:18]
      if (decoded_10) begin // @[CSR.scala 1209:40]
        reg_mepc <= _reg_mepc_T_2; // @[CSR.scala 1209:51]
      end else begin
        reg_mepc <= _GEN_211;
      end
    end else begin
      reg_mepc <= _GEN_211;
    end
    if (reset) begin // @[CSR.scala 474:27]
      reg_mcause <= 32'h0; // @[CSR.scala 474:27]
    end else if (csr_wen) begin // @[CSR.scala 1151:18]
      if (decoded_12) begin // @[CSR.scala 1213:40]
        reg_mcause <= _reg_mcause_T; // @[CSR.scala 1213:53]
      end else begin
        reg_mcause <= _GEN_212;
      end
    end else begin
      reg_mcause <= _GEN_212;
    end
    if (csr_wen) begin // @[CSR.scala 1151:18]
      if (decoded_11) begin // @[CSR.scala 1214:40]
        reg_mtval <= wdata; // @[CSR.scala 1214:52]
      end else begin
        reg_mtval <= _GEN_213;
      end
    end else begin
      reg_mtval <= _GEN_213;
    end
    if (csr_wen) begin // @[CSR.scala 1151:18]
      if (decoded_9) begin // @[CSR.scala 1210:40]
        reg_mscratch <= wdata; // @[CSR.scala 1210:55]
      end
    end
    if (reset) begin // @[CSR.scala 480:27]
      reg_mtvec <= 32'h0; // @[CSR.scala 480:27]
    end else if (csr_wen) begin // @[CSR.scala 1151:18]
      if (decoded_6) begin // @[CSR.scala 1212:40]
        reg_mtvec <= wdata; // @[CSR.scala 1212:52]
      end
    end
    if (reset) begin // @[CSR.scala 548:34]
      reg_mcountinhibit <= 3'h0; // @[CSR.scala 548:34]
    end else begin
      reg_mcountinhibit <= _GEN_449[2:0];
    end
    if (reset) begin // @[Counters.scala 45:37]
      small_ <= 6'h0; // @[Counters.scala 45:37]
    end else begin
      small_ <= _GEN_452[5:0];
    end
    if (reset) begin // @[Counters.scala 50:27]
      large_ <= 58'h0; // @[Counters.scala 50:27]
    end else if (csr_wen) begin // @[CSR.scala 1151:18]
      if (decoded_108) begin // @[CSR.scala 1559:31]
        large_ <= _T_2008[63:6]; // @[Counters.scala 66:23]
      end else if (decoded_19) begin // @[CSR.scala 1558:31]
        large_ <= _T_2005[63:6]; // @[Counters.scala 66:23]
      end else begin
        large_ <= _GEN_1;
      end
    end else begin
      large_ <= _GEN_1;
    end
    if (reset) begin // @[CSR.scala 606:21]
      reg_misa <= 32'h40801105; // @[CSR.scala 606:21]
    end else if (csr_wen) begin // @[CSR.scala 1151:18]
      if (decoded_4) begin // @[CSR.scala 1184:36]
        if (~io_pc[1] | wdata[2]) begin // @[CSR.scala 1188:64]
          reg_misa <= _reg_misa_T_8; // @[CSR.scala 1190:20]
        end
      end
    end
    if (reset) begin // @[CSR.scala 751:43]
      reg_custom_0 <= 32'h8; // @[CSR.scala 751:43]
    end else if (csr_wen) begin // @[CSR.scala 1151:18]
      if (decoded_129) begin // @[CSR.scala 1425:35]
        reg_custom_0 <= _reg_custom_0_T_3; // @[CSR.scala 1426:13]
      end
    end
    if (reset) begin // @[Reg.scala 28:20]
      io_status_cease_r <= 1'h0; // @[Reg.scala 28:20]
    end else begin
      io_status_cease_r <= _GEN_279;
    end
    `ifndef SYNTHESIS
    `ifdef STOP_COND
      if (`STOP_COND) begin
    `endif
        if (~(_T_252 <= 3'h1) & ~reset) begin
          $fatal; // @[CSR.scala 957:9]
        end
    `ifdef STOP_COND
      end
    `endif
    `endif // SYNTHESIS
    `ifndef SYNTHESIS
    `ifdef PRINTF_COND
      if (`PRINTF_COND) begin
    `endif
        if (~reset & ~(_T_252 <= 3'h1)) begin
          $fwrite(32'h80000002,
            "Assertion failed: these conditions must be mutually exclusive\n    at CSR.scala:957 assert(PopCount(insn_ret :: insn_call :: insn_break :: io.exception :: Nil) <= 1, \"these conditions must be mutually exclusive\")\n"
            ); // @[CSR.scala 957:9]
        end
    `ifdef PRINTF_COND
      end
    `endif
    `endif // SYNTHESIS
    `ifndef SYNTHESIS
    `ifdef STOP_COND
      if (`STOP_COND) begin
    `endif
        if (~(~reg_singleStepped | ~io_retire) & _T_256) begin
          $fatal; // @[CSR.scala 966:9]
        end
    `ifdef STOP_COND
      end
    `endif
    `endif // SYNTHESIS
    `ifndef SYNTHESIS
    `ifdef PRINTF_COND
      if (`PRINTF_COND) begin
    `endif
        if (_T_256 & ~(~reg_singleStepped | ~io_retire)) begin
          $fwrite(32'h80000002,
            "Assertion failed\n    at CSR.scala:966 assert(!reg_singleStepped || io.retire === UInt(0))\n"); // @[CSR.scala 966:9]
        end
    `ifdef PRINTF_COND
      end
    `endif
    `endif // SYNTHESIS
  end
  always @(posedge io_ungated_clock) begin
    if (reset) begin // @[CSR.scala 539:50]
      reg_wfi <= 1'h0; // @[CSR.scala 539:50]
    end else if (|pending_interrupts | io_interrupts_debug | exception) begin // @[CSR.scala 960:69]
      reg_wfi <= 1'h0; // @[CSR.scala 960:79]
    end else begin
      reg_wfi <= _GEN_46;
    end
    if (reset) begin // @[Counters.scala 45:37]
      small_1 <= 6'h0; // @[Counters.scala 45:37]
    end else begin
      small_1 <= _GEN_450[5:0];
    end
    if (reset) begin // @[Counters.scala 50:27]
      large_1 <= 58'h0; // @[Counters.scala 50:27]
    end else if (csr_wen) begin // @[CSR.scala 1151:18]
      if (decoded_107) begin // @[CSR.scala 1559:31]
        large_1 <= _T_2003[63:6]; // @[Counters.scala 66:23]
      end else if (decoded_18) begin // @[CSR.scala 1558:31]
        large_1 <= _T_2000[63:6]; // @[Counters.scala 66:23]
      end else begin
        large_1 <= _GEN_3;
      end
    end else begin
      large_1 <= _GEN_3;
    end
  end
// Register and memory initialization
`ifdef RANDOMIZE_GARBAGE_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_INVALID_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_REG_INIT
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_MEM_INIT
`define RANDOMIZE
`endif
`ifndef RANDOM
`define RANDOM $random
`endif
`ifdef RANDOMIZE_MEM_INIT
  integer initvar;
`endif
`ifndef SYNTHESIS
`ifdef FIRRTL_BEFORE_INITIAL
`FIRRTL_BEFORE_INITIAL
`endif
initial begin
  `ifdef RANDOMIZE
    `ifdef INIT_RANDOM
      `INIT_RANDOM
    `endif
    `ifndef VERILATOR
      `ifdef RANDOMIZE_DELAY
        #`RANDOMIZE_DELAY begin end
      `else
        #0.002 begin end
      `endif
    `endif
`ifdef RANDOMIZE_REG_INIT
  _RAND_0 = {1{`RANDOM}};
  reg_mstatus_gva = _RAND_0[0:0];
  _RAND_1 = {1{`RANDOM}};
  reg_mstatus_spp = _RAND_1[0:0];
  _RAND_2 = {1{`RANDOM}};
  reg_mstatus_mpie = _RAND_2[0:0];
  _RAND_3 = {1{`RANDOM}};
  reg_mstatus_mie = _RAND_3[0:0];
  _RAND_4 = {1{`RANDOM}};
  reg_dcsr_ebreakm = _RAND_4[0:0];
  _RAND_5 = {1{`RANDOM}};
  reg_dcsr_cause = _RAND_5[2:0];
  _RAND_6 = {1{`RANDOM}};
  reg_dcsr_step = _RAND_6[0:0];
  _RAND_7 = {1{`RANDOM}};
  reg_debug = _RAND_7[0:0];
  _RAND_8 = {1{`RANDOM}};
  reg_dpc = _RAND_8[31:0];
  _RAND_9 = {1{`RANDOM}};
  reg_dscratch0 = _RAND_9[31:0];
  _RAND_10 = {1{`RANDOM}};
  reg_singleStepped = _RAND_10[0:0];
  _RAND_11 = {1{`RANDOM}};
  reg_bp_0_control_dmode = _RAND_11[0:0];
  _RAND_12 = {1{`RANDOM}};
  reg_bp_0_control_action = _RAND_12[0:0];
  _RAND_13 = {1{`RANDOM}};
  reg_bp_0_control_tmatch = _RAND_13[1:0];
  _RAND_14 = {1{`RANDOM}};
  reg_bp_0_control_x = _RAND_14[0:0];
  _RAND_15 = {1{`RANDOM}};
  reg_bp_0_control_w = _RAND_15[0:0];
  _RAND_16 = {1{`RANDOM}};
  reg_bp_0_control_r = _RAND_16[0:0];
  _RAND_17 = {1{`RANDOM}};
  reg_bp_0_address = _RAND_17[31:0];
  _RAND_18 = {1{`RANDOM}};
  reg_pmp_0_cfg_l = _RAND_18[0:0];
  _RAND_19 = {1{`RANDOM}};
  reg_pmp_0_cfg_a = _RAND_19[1:0];
  _RAND_20 = {1{`RANDOM}};
  reg_pmp_0_cfg_x = _RAND_20[0:0];
  _RAND_21 = {1{`RANDOM}};
  reg_pmp_0_cfg_w = _RAND_21[0:0];
  _RAND_22 = {1{`RANDOM}};
  reg_pmp_0_cfg_r = _RAND_22[0:0];
  _RAND_23 = {1{`RANDOM}};
  reg_pmp_0_addr = _RAND_23[29:0];
  _RAND_24 = {1{`RANDOM}};
  reg_pmp_1_cfg_l = _RAND_24[0:0];
  _RAND_25 = {1{`RANDOM}};
  reg_pmp_1_cfg_a = _RAND_25[1:0];
  _RAND_26 = {1{`RANDOM}};
  reg_pmp_1_cfg_x = _RAND_26[0:0];
  _RAND_27 = {1{`RANDOM}};
  reg_pmp_1_cfg_w = _RAND_27[0:0];
  _RAND_28 = {1{`RANDOM}};
  reg_pmp_1_cfg_r = _RAND_28[0:0];
  _RAND_29 = {1{`RANDOM}};
  reg_pmp_1_addr = _RAND_29[29:0];
  _RAND_30 = {1{`RANDOM}};
  reg_pmp_2_cfg_l = _RAND_30[0:0];
  _RAND_31 = {1{`RANDOM}};
  reg_pmp_2_cfg_a = _RAND_31[1:0];
  _RAND_32 = {1{`RANDOM}};
  reg_pmp_2_cfg_x = _RAND_32[0:0];
  _RAND_33 = {1{`RANDOM}};
  reg_pmp_2_cfg_w = _RAND_33[0:0];
  _RAND_34 = {1{`RANDOM}};
  reg_pmp_2_cfg_r = _RAND_34[0:0];
  _RAND_35 = {1{`RANDOM}};
  reg_pmp_2_addr = _RAND_35[29:0];
  _RAND_36 = {1{`RANDOM}};
  reg_pmp_3_cfg_l = _RAND_36[0:0];
  _RAND_37 = {1{`RANDOM}};
  reg_pmp_3_cfg_a = _RAND_37[1:0];
  _RAND_38 = {1{`RANDOM}};
  reg_pmp_3_cfg_x = _RAND_38[0:0];
  _RAND_39 = {1{`RANDOM}};
  reg_pmp_3_cfg_w = _RAND_39[0:0];
  _RAND_40 = {1{`RANDOM}};
  reg_pmp_3_cfg_r = _RAND_40[0:0];
  _RAND_41 = {1{`RANDOM}};
  reg_pmp_3_addr = _RAND_41[29:0];
  _RAND_42 = {1{`RANDOM}};
  reg_pmp_4_cfg_l = _RAND_42[0:0];
  _RAND_43 = {1{`RANDOM}};
  reg_pmp_4_cfg_a = _RAND_43[1:0];
  _RAND_44 = {1{`RANDOM}};
  reg_pmp_4_cfg_x = _RAND_44[0:0];
  _RAND_45 = {1{`RANDOM}};
  reg_pmp_4_cfg_w = _RAND_45[0:0];
  _RAND_46 = {1{`RANDOM}};
  reg_pmp_4_cfg_r = _RAND_46[0:0];
  _RAND_47 = {1{`RANDOM}};
  reg_pmp_4_addr = _RAND_47[29:0];
  _RAND_48 = {1{`RANDOM}};
  reg_pmp_5_cfg_l = _RAND_48[0:0];
  _RAND_49 = {1{`RANDOM}};
  reg_pmp_5_cfg_a = _RAND_49[1:0];
  _RAND_50 = {1{`RANDOM}};
  reg_pmp_5_cfg_x = _RAND_50[0:0];
  _RAND_51 = {1{`RANDOM}};
  reg_pmp_5_cfg_w = _RAND_51[0:0];
  _RAND_52 = {1{`RANDOM}};
  reg_pmp_5_cfg_r = _RAND_52[0:0];
  _RAND_53 = {1{`RANDOM}};
  reg_pmp_5_addr = _RAND_53[29:0];
  _RAND_54 = {1{`RANDOM}};
  reg_pmp_6_cfg_l = _RAND_54[0:0];
  _RAND_55 = {1{`RANDOM}};
  reg_pmp_6_cfg_a = _RAND_55[1:0];
  _RAND_56 = {1{`RANDOM}};
  reg_pmp_6_cfg_x = _RAND_56[0:0];
  _RAND_57 = {1{`RANDOM}};
  reg_pmp_6_cfg_w = _RAND_57[0:0];
  _RAND_58 = {1{`RANDOM}};
  reg_pmp_6_cfg_r = _RAND_58[0:0];
  _RAND_59 = {1{`RANDOM}};
  reg_pmp_6_addr = _RAND_59[29:0];
  _RAND_60 = {1{`RANDOM}};
  reg_pmp_7_cfg_l = _RAND_60[0:0];
  _RAND_61 = {1{`RANDOM}};
  reg_pmp_7_cfg_a = _RAND_61[1:0];
  _RAND_62 = {1{`RANDOM}};
  reg_pmp_7_cfg_x = _RAND_62[0:0];
  _RAND_63 = {1{`RANDOM}};
  reg_pmp_7_cfg_w = _RAND_63[0:0];
  _RAND_64 = {1{`RANDOM}};
  reg_pmp_7_cfg_r = _RAND_64[0:0];
  _RAND_65 = {1{`RANDOM}};
  reg_pmp_7_addr = _RAND_65[29:0];
  _RAND_66 = {1{`RANDOM}};
  reg_mie = _RAND_66[31:0];
  _RAND_67 = {1{`RANDOM}};
  reg_mepc = _RAND_67[31:0];
  _RAND_68 = {1{`RANDOM}};
  reg_mcause = _RAND_68[31:0];
  _RAND_69 = {1{`RANDOM}};
  reg_mtval = _RAND_69[31:0];
  _RAND_70 = {1{`RANDOM}};
  reg_mscratch = _RAND_70[31:0];
  _RAND_71 = {1{`RANDOM}};
  reg_mtvec = _RAND_71[31:0];
  _RAND_72 = {1{`RANDOM}};
  reg_wfi = _RAND_72[0:0];
  _RAND_73 = {1{`RANDOM}};
  reg_mcountinhibit = _RAND_73[2:0];
  _RAND_74 = {1{`RANDOM}};
  small_ = _RAND_74[5:0];
  _RAND_75 = {2{`RANDOM}};
  large_ = _RAND_75[57:0];
  _RAND_76 = {1{`RANDOM}};
  small_1 = _RAND_76[5:0];
  _RAND_77 = {2{`RANDOM}};
  large_1 = _RAND_77[57:0];
  _RAND_78 = {1{`RANDOM}};
  reg_misa = _RAND_78[31:0];
  _RAND_79 = {1{`RANDOM}};
  reg_custom_0 = _RAND_79[31:0];
  _RAND_80 = {1{`RANDOM}};
  io_status_cease_r = _RAND_80[0:0];
`endif // RANDOMIZE_REG_INIT
  `endif // RANDOMIZE
end // initial
`ifdef FIRRTL_AFTER_INITIAL
`FIRRTL_AFTER_INITIAL
`endif
`endif // SYNTHESIS
endmodule
module BreakpointUnit(
  input         io_status_debug,
  input         io_bp_0_control_action,
  input  [1:0]  io_bp_0_control_tmatch,
  input         io_bp_0_control_x,
  input         io_bp_0_control_w,
  input         io_bp_0_control_r,
  input  [31:0] io_bp_0_address,
  input  [31:0] io_pc,
  input  [31:0] io_ea,
  output        io_xcpt_if,
  output        io_xcpt_ld,
  output        io_xcpt_st,
  output        io_debug_if,
  output        io_debug_ld,
  output        io_debug_st
);
  wire  en = ~io_status_debug; // @[Breakpoint.scala 30:35]
  wire  _r_T_4 = io_ea >= io_bp_0_address ^ io_bp_0_control_tmatch[0]; // @[Breakpoint.scala 65:20]
  wire [31:0] _r_T_5 = ~io_ea; // @[Breakpoint.scala 62:6]
  wire  _r_T_8 = io_bp_0_control_tmatch[0] & io_bp_0_address[0]; // @[Breakpoint.scala 59:73]
  wire  _r_T_10 = io_bp_0_control_tmatch[0] & io_bp_0_address[0] & io_bp_0_address[1]; // @[Breakpoint.scala 59:73]
  wire  _r_T_12 = io_bp_0_control_tmatch[0] & io_bp_0_address[0] & io_bp_0_address[1] & io_bp_0_address[2]; // @[Breakpoint.scala 59:73]
  wire [3:0] _r_T_13 = {_r_T_12,_r_T_10,_r_T_8,io_bp_0_control_tmatch[0]}; // @[Cat.scala 31:58]
  wire [31:0] _GEN_11 = {{28'd0}, _r_T_13}; // @[Breakpoint.scala 62:9]
  wire [31:0] _r_T_14 = _r_T_5 | _GEN_11; // @[Breakpoint.scala 62:9]
  wire [31:0] _r_T_15 = ~io_bp_0_address; // @[Breakpoint.scala 62:24]
  wire [31:0] _r_T_24 = _r_T_15 | _GEN_11; // @[Breakpoint.scala 62:33]
  wire  _r_T_25 = _r_T_14 == _r_T_24; // @[Breakpoint.scala 62:19]
  wire  _r_T_26 = io_bp_0_control_tmatch[1] ? _r_T_4 : _r_T_25; // @[Breakpoint.scala 68:8]
  wire  r = en & io_bp_0_control_r & _r_T_26; // @[Breakpoint.scala 106:32]
  wire  w = en & io_bp_0_control_w & _r_T_26; // @[Breakpoint.scala 107:32]
  wire  _x_T_4 = io_pc >= io_bp_0_address ^ io_bp_0_control_tmatch[0]; // @[Breakpoint.scala 65:20]
  wire [31:0] _x_T_5 = ~io_pc; // @[Breakpoint.scala 62:6]
  wire [31:0] _x_T_14 = _x_T_5 | _GEN_11; // @[Breakpoint.scala 62:9]
  wire  _x_T_25 = _x_T_14 == _r_T_24; // @[Breakpoint.scala 62:19]
  wire  _x_T_26 = io_bp_0_control_tmatch[1] ? _x_T_4 : _x_T_25; // @[Breakpoint.scala 68:8]
  wire  x = en & io_bp_0_control_x & _x_T_26; // @[Breakpoint.scala 108:32]
  wire  _io_xcpt_ld_T = ~io_bp_0_control_action; // @[Breakpoint.scala 118:51]
  assign io_xcpt_if = x & _io_xcpt_ld_T; // @[Breakpoint.scala 120:{27,40} 96:14]
  assign io_xcpt_ld = r & ~io_bp_0_control_action; // @[Breakpoint.scala 118:{27,40} 97:14]
  assign io_xcpt_st = w & _io_xcpt_ld_T; // @[Breakpoint.scala 119:{27,40} 98:14]
  assign io_debug_if = x & io_bp_0_control_action; // @[Breakpoint.scala 120:{27,73} 99:15]
  assign io_debug_ld = r & io_bp_0_control_action; // @[Breakpoint.scala 100:15 118:{27,73}]
  assign io_debug_st = w & io_bp_0_control_action; // @[Breakpoint.scala 101:15 119:{27,73}]
endmodule
module ALU(
  input  [3:0]  io_fn,
  input  [31:0] io_in2,
  input  [31:0] io_in1,
  output [31:0] io_out,
  output [31:0] io_adder_out,
  output        io_cmp_out
);
  wire [31:0] _in2_inv_T_1 = ~io_in2; // @[ALU.scala 62:35]
  wire [31:0] in2_inv = io_fn[3] ? _in2_inv_T_1 : io_in2; // @[ALU.scala 62:20]
  wire [31:0] in1_xor_in2 = io_in1 ^ in2_inv; // @[ALU.scala 63:28]
  wire [31:0] _io_adder_out_T_1 = io_in1 + in2_inv; // @[ALU.scala 64:26]
  wire [31:0] _GEN_0 = {{31'd0}, io_fn[3]}; // @[ALU.scala 64:36]
  wire  _slt_T_7 = io_fn[1] ? io_in2[31] : io_in1[31]; // @[ALU.scala 69:8]
  wire  slt = io_in1[31] == io_in2[31] ? io_adder_out[31] : _slt_T_7; // @[ALU.scala 68:8]
  wire  _io_cmp_out_T_2 = ~io_fn[3]; // @[ALU.scala 45:26]
  wire  _io_cmp_out_T_4 = _io_cmp_out_T_2 ? in1_xor_in2 == 32'h0 : slt; // @[ALU.scala 70:41]
  wire [4:0] shamt = io_in2[4:0]; // @[ALU.scala 74:28]
  wire  _shin_T_2 = io_fn == 4'h5 | io_fn == 4'hb; // @[ALU.scala 82:35]
  wire [31:0] _GEN_1 = {{16'd0}, io_in1[31:16]}; // @[Bitwise.scala 105:31]
  wire [31:0] _shin_T_6 = _GEN_1 & 32'hffff; // @[Bitwise.scala 105:31]
  wire [31:0] _shin_T_8 = {io_in1[15:0], 16'h0}; // @[Bitwise.scala 105:70]
  wire [31:0] _shin_T_10 = _shin_T_8 & 32'hffff0000; // @[Bitwise.scala 105:80]
  wire [31:0] _shin_T_11 = _shin_T_6 | _shin_T_10; // @[Bitwise.scala 105:39]
  wire [31:0] _GEN_2 = {{8'd0}, _shin_T_11[31:8]}; // @[Bitwise.scala 105:31]
  wire [31:0] _shin_T_16 = _GEN_2 & 32'hff00ff; // @[Bitwise.scala 105:31]
  wire [31:0] _shin_T_18 = {_shin_T_11[23:0], 8'h0}; // @[Bitwise.scala 105:70]
  wire [31:0] _shin_T_20 = _shin_T_18 & 32'hff00ff00; // @[Bitwise.scala 105:80]
  wire [31:0] _shin_T_21 = _shin_T_16 | _shin_T_20; // @[Bitwise.scala 105:39]
  wire [31:0] _GEN_3 = {{4'd0}, _shin_T_21[31:4]}; // @[Bitwise.scala 105:31]
  wire [31:0] _shin_T_26 = _GEN_3 & 32'hf0f0f0f; // @[Bitwise.scala 105:31]
  wire [31:0] _shin_T_28 = {_shin_T_21[27:0], 4'h0}; // @[Bitwise.scala 105:70]
  wire [31:0] _shin_T_30 = _shin_T_28 & 32'hf0f0f0f0; // @[Bitwise.scala 105:80]
  wire [31:0] _shin_T_31 = _shin_T_26 | _shin_T_30; // @[Bitwise.scala 105:39]
  wire [31:0] _GEN_4 = {{2'd0}, _shin_T_31[31:2]}; // @[Bitwise.scala 105:31]
  wire [31:0] _shin_T_36 = _GEN_4 & 32'h33333333; // @[Bitwise.scala 105:31]
  wire [31:0] _shin_T_38 = {_shin_T_31[29:0], 2'h0}; // @[Bitwise.scala 105:70]
  wire [31:0] _shin_T_40 = _shin_T_38 & 32'hcccccccc; // @[Bitwise.scala 105:80]
  wire [31:0] _shin_T_41 = _shin_T_36 | _shin_T_40; // @[Bitwise.scala 105:39]
  wire [31:0] _GEN_5 = {{1'd0}, _shin_T_41[31:1]}; // @[Bitwise.scala 105:31]
  wire [31:0] _shin_T_46 = _GEN_5 & 32'h55555555; // @[Bitwise.scala 105:31]
  wire [31:0] _shin_T_48 = {_shin_T_41[30:0], 1'h0}; // @[Bitwise.scala 105:70]
  wire [31:0] _shin_T_50 = _shin_T_48 & 32'haaaaaaaa; // @[Bitwise.scala 105:80]
  wire [31:0] _shin_T_51 = _shin_T_46 | _shin_T_50; // @[Bitwise.scala 105:39]
  wire [31:0] shin = io_fn == 4'h5 | io_fn == 4'hb ? io_in1 : _shin_T_51; // @[ALU.scala 82:17]
  wire  _shout_r_T_2 = io_fn[3] & shin[31]; // @[ALU.scala 83:35]
  wire [32:0] _shout_r_T_4 = {_shout_r_T_2,shin}; // @[ALU.scala 83:57]
  wire [32:0] _shout_r_T_5 = $signed(_shout_r_T_4) >>> shamt; // @[ALU.scala 83:64]
  wire [31:0] shout_r = _shout_r_T_5[31:0]; // @[ALU.scala 83:73]
  wire [31:0] _GEN_6 = {{16'd0}, shout_r[31:16]}; // @[Bitwise.scala 105:31]
  wire [31:0] _shout_l_T_3 = _GEN_6 & 32'hffff; // @[Bitwise.scala 105:31]
  wire [31:0] _shout_l_T_5 = {shout_r[15:0], 16'h0}; // @[Bitwise.scala 105:70]
  wire [31:0] _shout_l_T_7 = _shout_l_T_5 & 32'hffff0000; // @[Bitwise.scala 105:80]
  wire [31:0] _shout_l_T_8 = _shout_l_T_3 | _shout_l_T_7; // @[Bitwise.scala 105:39]
  wire [31:0] _GEN_7 = {{8'd0}, _shout_l_T_8[31:8]}; // @[Bitwise.scala 105:31]
  wire [31:0] _shout_l_T_13 = _GEN_7 & 32'hff00ff; // @[Bitwise.scala 105:31]
  wire [31:0] _shout_l_T_15 = {_shout_l_T_8[23:0], 8'h0}; // @[Bitwise.scala 105:70]
  wire [31:0] _shout_l_T_17 = _shout_l_T_15 & 32'hff00ff00; // @[Bitwise.scala 105:80]
  wire [31:0] _shout_l_T_18 = _shout_l_T_13 | _shout_l_T_17; // @[Bitwise.scala 105:39]
  wire [31:0] _GEN_8 = {{4'd0}, _shout_l_T_18[31:4]}; // @[Bitwise.scala 105:31]
  wire [31:0] _shout_l_T_23 = _GEN_8 & 32'hf0f0f0f; // @[Bitwise.scala 105:31]
  wire [31:0] _shout_l_T_25 = {_shout_l_T_18[27:0], 4'h0}; // @[Bitwise.scala 105:70]
  wire [31:0] _shout_l_T_27 = _shout_l_T_25 & 32'hf0f0f0f0; // @[Bitwise.scala 105:80]
  wire [31:0] _shout_l_T_28 = _shout_l_T_23 | _shout_l_T_27; // @[Bitwise.scala 105:39]
  wire [31:0] _GEN_9 = {{2'd0}, _shout_l_T_28[31:2]}; // @[Bitwise.scala 105:31]
  wire [31:0] _shout_l_T_33 = _GEN_9 & 32'h33333333; // @[Bitwise.scala 105:31]
  wire [31:0] _shout_l_T_35 = {_shout_l_T_28[29:0], 2'h0}; // @[Bitwise.scala 105:70]
  wire [31:0] _shout_l_T_37 = _shout_l_T_35 & 32'hcccccccc; // @[Bitwise.scala 105:80]
  wire [31:0] _shout_l_T_38 = _shout_l_T_33 | _shout_l_T_37; // @[Bitwise.scala 105:39]
  wire [31:0] _GEN_10 = {{1'd0}, _shout_l_T_38[31:1]}; // @[Bitwise.scala 105:31]
  wire [31:0] _shout_l_T_43 = _GEN_10 & 32'h55555555; // @[Bitwise.scala 105:31]
  wire [31:0] _shout_l_T_45 = {_shout_l_T_38[30:0], 1'h0}; // @[Bitwise.scala 105:70]
  wire [31:0] _shout_l_T_47 = _shout_l_T_45 & 32'haaaaaaaa; // @[Bitwise.scala 105:80]
  wire [31:0] shout_l = _shout_l_T_43 | _shout_l_T_47; // @[Bitwise.scala 105:39]
  wire [31:0] _shout_T_3 = _shin_T_2 ? shout_r : 32'h0; // @[ALU.scala 85:18]
  wire [31:0] _shout_T_5 = io_fn == 4'h1 ? shout_l : 32'h0; // @[ALU.scala 86:18]
  wire [31:0] shout = _shout_T_3 | _shout_T_5; // @[ALU.scala 85:70]
  wire  _logic_T_1 = io_fn == 4'h6; // @[ALU.scala 89:45]
  wire [31:0] _logic_T_3 = io_fn == 4'h4 | io_fn == 4'h6 ? in1_xor_in2 : 32'h0; // @[ALU.scala 89:18]
  wire [31:0] _logic_T_7 = io_in1 & io_in2; // @[ALU.scala 90:63]
  wire [31:0] _logic_T_8 = _logic_T_1 | io_fn == 4'h7 ? _logic_T_7 : 32'h0; // @[ALU.scala 90:18]
  wire [31:0] logic_ = _logic_T_3 | _logic_T_8; // @[ALU.scala 89:74]
  wire  _shift_logic_T = io_fn >= 4'hc; // @[ALU.scala 42:30]
  wire  _shift_logic_T_1 = _shift_logic_T & slt; // @[ALU.scala 91:35]
  wire [31:0] _GEN_11 = {{31'd0}, _shift_logic_T_1}; // @[ALU.scala 91:43]
  wire [31:0] _shift_logic_T_2 = _GEN_11 | logic_; // @[ALU.scala 91:43]
  wire [31:0] shift_logic = _shift_logic_T_2 | shout; // @[ALU.scala 91:51]
  assign io_out = io_fn == 4'h0 | io_fn == 4'ha ? io_adder_out : shift_logic; // @[ALU.scala 92:16]
  assign io_adder_out = _io_adder_out_T_1 + _GEN_0; // @[ALU.scala 64:36]
  assign io_cmp_out = io_fn[0] ^ _io_cmp_out_T_4; // @[ALU.scala 70:36]
endmodule
module MulDiv(
  input         clock,
  input         reset,
  output        io_req_ready,
  input         io_req_valid,
  input  [3:0]  io_req_bits_fn,
  input  [31:0] io_req_bits_in1,
  input  [31:0] io_req_bits_in2,
  input  [4:0]  io_req_bits_tag,
  input         io_kill,
  input         io_resp_ready,
  output        io_resp_valid,
  output [31:0] io_resp_bits_data,
  output [4:0]  io_resp_bits_tag
);
`ifdef RANDOMIZE_REG_INIT
  reg [31:0] _RAND_0;
  reg [31:0] _RAND_1;
  reg [31:0] _RAND_2;
  reg [31:0] _RAND_3;
  reg [31:0] _RAND_4;
  reg [31:0] _RAND_5;
  reg [63:0] _RAND_6;
  reg [95:0] _RAND_7;
`endif // RANDOMIZE_REG_INIT
  reg [2:0] state; // @[Multiplier.scala 50:22]
  reg [4:0] req_tag; // @[Multiplier.scala 52:16]
  reg [5:0] count; // @[Multiplier.scala 53:18]
  reg  neg_out; // @[Multiplier.scala 56:20]
  reg  isHi; // @[Multiplier.scala 57:17]
  reg  resHi; // @[Multiplier.scala 58:18]
  reg [32:0] divisor; // @[Multiplier.scala 59:20]
  reg [65:0] remainder; // @[Multiplier.scala 60:22]
  wire [2:0] decoded_plaInput = io_req_bits_fn[2:0]; // @[decoder.scala 38:16 pla.scala 77:22]
  wire [2:0] decoded_invInputs = ~decoded_plaInput; // @[pla.scala 78:21]
  wire  decoded_andMatrixInput_0 = decoded_invInputs[0]; // @[pla.scala 91:29]
  wire  _decoded_T = &decoded_andMatrixInput_0; // @[pla.scala 98:74]
  wire  decoded_andMatrixInput_0_1 = decoded_invInputs[2]; // @[pla.scala 91:29]
  wire  _decoded_T_1 = &decoded_andMatrixInput_0_1; // @[pla.scala 98:74]
  wire  decoded_andMatrixInput_0_2 = decoded_invInputs[1]; // @[pla.scala 91:29]
  wire [1:0] _decoded_T_2 = {decoded_andMatrixInput_0_2,decoded_andMatrixInput_0_1}; // @[Cat.scala 31:58]
  wire  _decoded_T_3 = &_decoded_T_2; // @[pla.scala 98:74]
  wire  decoded_andMatrixInput_0_3 = decoded_plaInput[0]; // @[pla.scala 90:45]
  wire [1:0] _decoded_T_4 = {decoded_andMatrixInput_0_3,decoded_andMatrixInput_0_1}; // @[Cat.scala 31:58]
  wire  _decoded_T_5 = &_decoded_T_4; // @[pla.scala 98:74]
  wire  decoded_andMatrixInput_0_4 = decoded_plaInput[1]; // @[pla.scala 90:45]
  wire  _decoded_T_6 = &decoded_andMatrixInput_0_4; // @[pla.scala 98:74]
  wire  decoded_andMatrixInput_1_2 = decoded_plaInput[2]; // @[pla.scala 90:45]
  wire [1:0] _decoded_T_7 = {decoded_andMatrixInput_0,decoded_andMatrixInput_1_2}; // @[Cat.scala 31:58]
  wire  _decoded_T_8 = &_decoded_T_7; // @[pla.scala 98:74]
  wire [1:0] _decoded_orMatrixOutputs_T = {_decoded_T_3,_decoded_T_8}; // @[Cat.scala 31:58]
  wire  _decoded_orMatrixOutputs_T_1 = |_decoded_orMatrixOutputs_T; // @[pla.scala 114:39]
  wire [1:0] _decoded_orMatrixOutputs_T_2 = {_decoded_T,_decoded_T_3}; // @[Cat.scala 31:58]
  wire  _decoded_orMatrixOutputs_T_3 = |_decoded_orMatrixOutputs_T_2; // @[pla.scala 114:39]
  wire [1:0] _decoded_orMatrixOutputs_T_4 = {_decoded_T_5,_decoded_T_6}; // @[Cat.scala 31:58]
  wire  _decoded_orMatrixOutputs_T_5 = |_decoded_orMatrixOutputs_T_4; // @[pla.scala 114:39]
  wire  _decoded_orMatrixOutputs_T_6 = |_decoded_T_1; // @[pla.scala 114:39]
  wire [3:0] decoded_orMatrixOutputs = {_decoded_orMatrixOutputs_T_6,_decoded_orMatrixOutputs_T_5,
    _decoded_orMatrixOutputs_T_3,_decoded_orMatrixOutputs_T_1}; // @[Cat.scala 31:58]
  wire [3:0] decoded_invMatrixOutputs = {decoded_orMatrixOutputs[3],decoded_orMatrixOutputs[2],decoded_orMatrixOutputs[1
    ],decoded_orMatrixOutputs[0]}; // @[Cat.scala 31:58]
  wire  cmdMul = decoded_invMatrixOutputs[3]; // @[Decode.scala 50:77]
  wire  cmdHi = decoded_invMatrixOutputs[2]; // @[Decode.scala 50:77]
  wire  lhsSigned = decoded_invMatrixOutputs[1]; // @[Decode.scala 50:77]
  wire  rhsSigned = decoded_invMatrixOutputs[0]; // @[Decode.scala 50:77]
  wire  lhs_sign = lhsSigned & io_req_bits_in1[31]; // @[Multiplier.scala 80:23]
  wire [15:0] hi = io_req_bits_in1[31:16]; // @[Multiplier.scala 81:43]
  wire [31:0] lhs_in = {hi,io_req_bits_in1[15:0]}; // @[Cat.scala 31:58]
  wire  rhs_sign = rhsSigned & io_req_bits_in2[31]; // @[Multiplier.scala 80:23]
  wire [15:0] hi_1 = io_req_bits_in2[31:16]; // @[Multiplier.scala 81:43]
  wire [32:0] subtractor = remainder[64:32] - divisor; // @[Multiplier.scala 87:37]
  wire [31:0] result = resHi ? remainder[64:33] : remainder[31:0]; // @[Multiplier.scala 88:19]
  wire [31:0] negated_remainder = 32'h0 - result; // @[Multiplier.scala 89:27]
  wire [65:0] _GEN_0 = remainder[31] ? {{34'd0}, negated_remainder} : remainder; // @[Multiplier.scala 92:27 93:17 60:22]
  wire [65:0] _GEN_2 = state == 3'h1 ? _GEN_0 : remainder; // @[Multiplier.scala 60:22 91:57]
  wire [2:0] _GEN_4 = state == 3'h1 ? 3'h3 : state; // @[Multiplier.scala 91:57 98:11 50:22]
  wire [2:0] _GEN_6 = state == 3'h5 ? 3'h7 : _GEN_4; // @[Multiplier.scala 100:57 102:11]
  wire  _GEN_7 = state == 3'h5 ? 1'h0 : resHi; // @[Multiplier.scala 100:57 103:11 58:18]
  wire [64:0] mulReg = {remainder[65:33],remainder[31:0]}; // @[Cat.scala 31:58]
  wire  mplierSign = remainder[32]; // @[Multiplier.scala 107:31]
  wire [31:0] mplier = mulReg[31:0]; // @[Multiplier.scala 108:24]
  wire [32:0] accum = mulReg[64:32]; // @[Multiplier.scala 109:37]
  wire [8:0] _prod_T_2 = {mplierSign,mplier[7:0]}; // @[Multiplier.scala 111:60]
  wire [41:0] _prod_T_3 = $signed(_prod_T_2) * $signed(divisor); // @[Multiplier.scala 111:67]
  wire [41:0] _GEN_35 = {{9{accum[32]}},accum}; // @[Multiplier.scala 111:76]
  wire [41:0] nextMulReg_hi = $signed(_prod_T_3) + $signed(_GEN_35); // @[Cat.scala 31:58]
  wire [65:0] nextMulReg = {nextMulReg_hi,mplier[31:8]}; // @[Cat.scala 31:58]
  wire  nextMplierSign = count == 6'h2 & neg_out; // @[Multiplier.scala 113:57]
  wire  _eOut_T_4 = ~isHi; // @[Multiplier.scala 117:7]
  wire [64:0] nextMulReg1 = {nextMulReg[64:32],nextMulReg[31:0]}; // @[Cat.scala 31:58]
  wire [65:0] _remainder_T_2 = {nextMulReg1[64:32],nextMplierSign,nextMulReg1[31:0]}; // @[Cat.scala 31:58]
  wire [5:0] _count_T_1 = count + 6'h1; // @[Multiplier.scala 122:20]
  wire [2:0] _GEN_8 = count == 6'h3 ? 3'h6 : _GEN_6; // @[Multiplier.scala 123:51 124:13]
  wire  _GEN_9 = count == 6'h3 ? isHi : _GEN_7; // @[Multiplier.scala 123:51 125:13]
  wire [2:0] _GEN_12 = state == 3'h2 ? _GEN_8 : _GEN_6; // @[Multiplier.scala 105:50]
  wire  _GEN_13 = state == 3'h2 ? _GEN_9 : _GEN_7; // @[Multiplier.scala 105:50]
  wire  unrolls_less = subtractor[32]; // @[Multiplier.scala 132:28]
  wire [31:0] _unrolls_T_2 = unrolls_less ? remainder[63:32] : subtractor[31:0]; // @[Multiplier.scala 133:14]
  wire  _unrolls_T_4 = ~unrolls_less; // @[Multiplier.scala 133:67]
  wire [64:0] unrolls_0 = {_unrolls_T_2,remainder[31:0],_unrolls_T_4}; // @[Cat.scala 31:58]
  wire [2:0] _state_T = neg_out ? 3'h5 : 3'h7; // @[Multiplier.scala 138:19]
  wire [2:0] _GEN_14 = count == 6'h20 ? _state_T : _GEN_12; // @[Multiplier.scala 137:38 138:13]
  wire  divby0 = count == 6'h0 & _unrolls_T_4; // @[Multiplier.scala 145:30]
  wire  _T_21 = io_resp_ready & io_resp_valid; // @[Decoupled.scala 50:35]
  wire  _T_23 = io_req_ready & io_req_valid; // @[Decoupled.scala 50:35]
  wire [32:0] _divisor_T = {rhs_sign,hi_1,io_req_bits_in2[15:0]}; // @[Cat.scala 31:58]
  wire [15:0] loOut = result[15:0]; // @[Multiplier.scala 175:82]
  assign io_req_ready = state == 3'h0; // @[Multiplier.scala 181:25]
  assign io_resp_valid = state == 3'h6 | state == 3'h7; // @[Multiplier.scala 180:42]
  assign io_resp_bits_data = {result[31:16],loOut}; // @[Cat.scala 31:58]
  assign io_resp_bits_tag = req_tag; // @[Multiplier.scala 177:20]
  always @(posedge clock) begin
    if (reset) begin // @[Multiplier.scala 50:22]
      state <= 3'h0; // @[Multiplier.scala 50:22]
    end else if (_T_23) begin // @[Multiplier.scala 163:24]
      if (cmdMul) begin // @[Multiplier.scala 164:17]
        state <= 3'h2;
      end else if (lhs_sign | rhs_sign) begin // @[Multiplier.scala 164:36]
        state <= 3'h1;
      end else begin
        state <= 3'h3;
      end
    end else if (_T_21 | io_kill) begin // @[Multiplier.scala 160:36]
      state <= 3'h0; // @[Multiplier.scala 161:11]
    end else if (state == 3'h3) begin // @[Multiplier.scala 128:50]
      state <= _GEN_14;
    end else begin
      state <= _GEN_12;
    end
    if (_T_23) begin // @[Multiplier.scala 163:24]
      req_tag <= io_req_bits_tag; // @[Multiplier.scala 171:9]
    end
    if (_T_23) begin // @[Multiplier.scala 163:24]
      count <= 6'h0; // @[Multiplier.scala 167:11]
    end else if (state == 3'h3) begin // @[Multiplier.scala 128:50]
      count <= _count_T_1; // @[Multiplier.scala 143:11]
    end else if (state == 3'h2) begin // @[Multiplier.scala 105:50]
      count <= _count_T_1; // @[Multiplier.scala 122:11]
    end
    if (_T_23) begin // @[Multiplier.scala 163:24]
      if (cmdHi) begin // @[Multiplier.scala 168:19]
        neg_out <= lhs_sign;
      end else begin
        neg_out <= lhs_sign != rhs_sign;
      end
    end else if (state == 3'h3) begin // @[Multiplier.scala 128:50]
      if (divby0 & _eOut_T_4) begin // @[Multiplier.scala 158:28]
        neg_out <= 1'h0; // @[Multiplier.scala 158:38]
      end
    end
    if (_T_23) begin // @[Multiplier.scala 163:24]
      isHi <= cmdHi; // @[Multiplier.scala 165:10]
    end
    if (_T_23) begin // @[Multiplier.scala 163:24]
      resHi <= 1'h0; // @[Multiplier.scala 166:11]
    end else if (state == 3'h3) begin // @[Multiplier.scala 128:50]
      if (count == 6'h20) begin // @[Multiplier.scala 137:38]
        resHi <= isHi; // @[Multiplier.scala 139:13]
      end else begin
        resHi <= _GEN_13;
      end
    end else begin
      resHi <= _GEN_13;
    end
    if (_T_23) begin // @[Multiplier.scala 163:24]
      divisor <= _divisor_T; // @[Multiplier.scala 169:13]
    end else if (state == 3'h1) begin // @[Multiplier.scala 91:57]
      if (divisor[31]) begin // @[Multiplier.scala 95:25]
        divisor <= subtractor; // @[Multiplier.scala 96:15]
      end
    end
    if (_T_23) begin // @[Multiplier.scala 163:24]
      remainder <= {{34'd0}, lhs_in}; // @[Multiplier.scala 170:15]
    end else if (state == 3'h3) begin // @[Multiplier.scala 128:50]
      remainder <= {{1'd0}, unrolls_0}; // @[Multiplier.scala 136:15]
    end else if (state == 3'h2) begin // @[Multiplier.scala 105:50]
      remainder <= _remainder_T_2; // @[Multiplier.scala 120:15]
    end else if (state == 3'h5) begin // @[Multiplier.scala 100:57]
      remainder <= {{34'd0}, negated_remainder}; // @[Multiplier.scala 101:15]
    end else begin
      remainder <= _GEN_2;
    end
  end
// Register and memory initialization
`ifdef RANDOMIZE_GARBAGE_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_INVALID_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_REG_INIT
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_MEM_INIT
`define RANDOMIZE
`endif
`ifndef RANDOM
`define RANDOM $random
`endif
`ifdef RANDOMIZE_MEM_INIT
  integer initvar;
`endif
`ifndef SYNTHESIS
`ifdef FIRRTL_BEFORE_INITIAL
`FIRRTL_BEFORE_INITIAL
`endif
initial begin
  `ifdef RANDOMIZE
    `ifdef INIT_RANDOM
      `INIT_RANDOM
    `endif
    `ifndef VERILATOR
      `ifdef RANDOMIZE_DELAY
        #`RANDOMIZE_DELAY begin end
      `else
        #0.002 begin end
      `endif
    `endif
`ifdef RANDOMIZE_REG_INIT
  _RAND_0 = {1{`RANDOM}};
  state = _RAND_0[2:0];
  _RAND_1 = {1{`RANDOM}};
  req_tag = _RAND_1[4:0];
  _RAND_2 = {1{`RANDOM}};
  count = _RAND_2[5:0];
  _RAND_3 = {1{`RANDOM}};
  neg_out = _RAND_3[0:0];
  _RAND_4 = {1{`RANDOM}};
  isHi = _RAND_4[0:0];
  _RAND_5 = {1{`RANDOM}};
  resHi = _RAND_5[0:0];
  _RAND_6 = {2{`RANDOM}};
  divisor = _RAND_6[32:0];
  _RAND_7 = {3{`RANDOM}};
  remainder = _RAND_7[65:0];
`endif // RANDOMIZE_REG_INIT
  `endif // RANDOMIZE
end // initial
`ifdef FIRRTL_AFTER_INITIAL
`FIRRTL_AFTER_INITIAL
`endif
`endif // SYNTHESIS
endmodule
module PlusArgTimeout(
  input         clock,
  input         reset,
  input  [31:0] io_count
);
  wire [31:0] plusarg_reader_out; // @[PlusArg.scala 62:19]
  wire  _T = plusarg_reader_out > 32'h0; // @[PlusArg.scala 63:13]
  plusarg_reader #(.FORMAT("max_core_cycles=%d"), .DEFAULT(0), .WIDTH(32)) plusarg_reader ( // @[PlusArg.scala 62:19]
    .out(plusarg_reader_out)
  );
  always @(posedge clock) begin
    `ifndef SYNTHESIS
    `ifdef STOP_COND
      if (`STOP_COND) begin
    `endif
        if (~(io_count < plusarg_reader_out) & (_T & ~reset)) begin
          $fatal; // @[PlusArg.scala 64:12]
        end
    `ifdef STOP_COND
      end
    `endif
    `endif // SYNTHESIS
    `ifndef SYNTHESIS
    `ifdef PRINTF_COND
      if (`PRINTF_COND) begin
    `endif
        if (_T & ~reset & ~(io_count < plusarg_reader_out)) begin
          $fwrite(32'h80000002,
            "Assertion failed: Timeout exceeded: Kill the emulation after INT rdtime cycles. Off if 0.\n    at PlusArg.scala:64 assert (io.count < max, s\"Timeout exceeded: $docstring\")\n"
            ); // @[PlusArg.scala 64:12]
        end
    `ifdef PRINTF_COND
      end
    `endif
    `endif // SYNTHESIS
  end
endmodule
module Rocket(
  input         clock,
  input         reset,
  input         io_hartid,
  input         io_interrupts_debug,
  input         io_interrupts_mtip,
  input         io_interrupts_msip,
  input         io_interrupts_meip,
  output        io_imem_might_request,
  output        io_imem_req_valid,
  output [31:0] io_imem_req_bits_pc,
  output        io_imem_req_bits_speculative,
  output        io_imem_resp_ready,
  input         io_imem_resp_valid,
  input  [31:0] io_imem_resp_bits_pc,
  input  [31:0] io_imem_resp_bits_data,
  input         io_imem_resp_bits_xcpt_ae_inst,
  input         io_imem_resp_bits_replay,
  output        io_imem_btb_update_valid,
  output        io_imem_bht_update_valid,
  output        io_imem_flush_icache,
  input         io_dmem_req_ready,
  output        io_dmem_req_valid,
  output [31:0] io_dmem_req_bits_addr,
  output [6:0]  io_dmem_req_bits_tag,
  output [4:0]  io_dmem_req_bits_cmd,
  output [1:0]  io_dmem_req_bits_size,
  output        io_dmem_req_bits_signed,
  output        io_dmem_req_bits_dv,
  output        io_dmem_s1_kill,
  output [31:0] io_dmem_s1_data_data,
  input         io_dmem_s2_nack,
  input         io_dmem_resp_valid,
  input  [6:0]  io_dmem_resp_bits_tag,
  input  [31:0] io_dmem_resp_bits_data,
  input         io_dmem_resp_bits_replay,
  input         io_dmem_resp_bits_has_data,
  input  [31:0] io_dmem_resp_bits_data_word_bypass,
  input         io_dmem_replay_next,
  input         io_dmem_s2_xcpt_ma_ld,
  input         io_dmem_s2_xcpt_ma_st,
  input         io_dmem_s2_xcpt_pf_ld,
  input         io_dmem_s2_xcpt_pf_st,
  input         io_dmem_s2_xcpt_ae_ld,
  input         io_dmem_s2_xcpt_ae_st,
  input         io_dmem_ordered,
  input         io_dmem_perf_grant,
  output        io_ptw_status_debug,
  output        io_ptw_pmp_0_cfg_l,
  output [1:0]  io_ptw_pmp_0_cfg_a,
  output        io_ptw_pmp_0_cfg_x,
  output        io_ptw_pmp_0_cfg_w,
  output        io_ptw_pmp_0_cfg_r,
  output [29:0] io_ptw_pmp_0_addr,
  output [31:0] io_ptw_pmp_0_mask,
  output        io_ptw_pmp_1_cfg_l,
  output [1:0]  io_ptw_pmp_1_cfg_a,
  output        io_ptw_pmp_1_cfg_x,
  output        io_ptw_pmp_1_cfg_w,
  output        io_ptw_pmp_1_cfg_r,
  output [29:0] io_ptw_pmp_1_addr,
  output [31:0] io_ptw_pmp_1_mask,
  output        io_ptw_pmp_2_cfg_l,
  output [1:0]  io_ptw_pmp_2_cfg_a,
  output        io_ptw_pmp_2_cfg_x,
  output        io_ptw_pmp_2_cfg_w,
  output        io_ptw_pmp_2_cfg_r,
  output [29:0] io_ptw_pmp_2_addr,
  output [31:0] io_ptw_pmp_2_mask,
  output        io_ptw_pmp_3_cfg_l,
  output [1:0]  io_ptw_pmp_3_cfg_a,
  output        io_ptw_pmp_3_cfg_x,
  output        io_ptw_pmp_3_cfg_w,
  output        io_ptw_pmp_3_cfg_r,
  output [29:0] io_ptw_pmp_3_addr,
  output [31:0] io_ptw_pmp_3_mask,
  output        io_ptw_pmp_4_cfg_l,
  output [1:0]  io_ptw_pmp_4_cfg_a,
  output        io_ptw_pmp_4_cfg_x,
  output        io_ptw_pmp_4_cfg_w,
  output        io_ptw_pmp_4_cfg_r,
  output [29:0] io_ptw_pmp_4_addr,
  output [31:0] io_ptw_pmp_4_mask,
  output        io_ptw_pmp_5_cfg_l,
  output [1:0]  io_ptw_pmp_5_cfg_a,
  output        io_ptw_pmp_5_cfg_x,
  output        io_ptw_pmp_5_cfg_w,
  output        io_ptw_pmp_5_cfg_r,
  output [29:0] io_ptw_pmp_5_addr,
  output [31:0] io_ptw_pmp_5_mask,
  output        io_ptw_pmp_6_cfg_l,
  output [1:0]  io_ptw_pmp_6_cfg_a,
  output        io_ptw_pmp_6_cfg_x,
  output        io_ptw_pmp_6_cfg_w,
  output        io_ptw_pmp_6_cfg_r,
  output [29:0] io_ptw_pmp_6_addr,
  output [31:0] io_ptw_pmp_6_mask,
  output        io_ptw_pmp_7_cfg_l,
  output [1:0]  io_ptw_pmp_7_cfg_a,
  output        io_ptw_pmp_7_cfg_x,
  output        io_ptw_pmp_7_cfg_w,
  output        io_ptw_pmp_7_cfg_r,
  output [29:0] io_ptw_pmp_7_addr,
  output [31:0] io_ptw_pmp_7_mask,
  output [31:0] io_ptw_customCSRs_csrs_0_value,
  output        io_rocc_cmd_valid,
  output        io_wfi
);
`ifdef RANDOMIZE_GARBAGE_ASSIGN
  reg [31:0] _RAND_1;
  reg [31:0] _RAND_2;
`endif // RANDOMIZE_GARBAGE_ASSIGN
`ifdef RANDOMIZE_MEM_INIT
  reg [31:0] _RAND_0;
`endif // RANDOMIZE_MEM_INIT
`ifdef RANDOMIZE_REG_INIT
  reg [31:0] _RAND_3;
  reg [31:0] _RAND_4;
  reg [31:0] _RAND_5;
  reg [31:0] _RAND_6;
  reg [31:0] _RAND_7;
  reg [31:0] _RAND_8;
  reg [31:0] _RAND_9;
  reg [31:0] _RAND_10;
  reg [31:0] _RAND_11;
  reg [31:0] _RAND_12;
  reg [31:0] _RAND_13;
  reg [31:0] _RAND_14;
  reg [31:0] _RAND_15;
  reg [31:0] _RAND_16;
  reg [31:0] _RAND_17;
  reg [31:0] _RAND_18;
  reg [31:0] _RAND_19;
  reg [31:0] _RAND_20;
  reg [31:0] _RAND_21;
  reg [31:0] _RAND_22;
  reg [31:0] _RAND_23;
  reg [31:0] _RAND_24;
  reg [31:0] _RAND_25;
  reg [31:0] _RAND_26;
  reg [31:0] _RAND_27;
  reg [31:0] _RAND_28;
  reg [31:0] _RAND_29;
  reg [31:0] _RAND_30;
  reg [31:0] _RAND_31;
  reg [31:0] _RAND_32;
  reg [31:0] _RAND_33;
  reg [31:0] _RAND_34;
  reg [31:0] _RAND_35;
  reg [31:0] _RAND_36;
  reg [31:0] _RAND_37;
  reg [31:0] _RAND_38;
  reg [31:0] _RAND_39;
  reg [31:0] _RAND_40;
  reg [31:0] _RAND_41;
  reg [31:0] _RAND_42;
  reg [31:0] _RAND_43;
  reg [31:0] _RAND_44;
  reg [31:0] _RAND_45;
  reg [31:0] _RAND_46;
  reg [31:0] _RAND_47;
  reg [31:0] _RAND_48;
  reg [31:0] _RAND_49;
  reg [31:0] _RAND_50;
  reg [31:0] _RAND_51;
  reg [31:0] _RAND_52;
  reg [31:0] _RAND_53;
  reg [31:0] _RAND_54;
  reg [31:0] _RAND_55;
  reg [31:0] _RAND_56;
  reg [31:0] _RAND_57;
  reg [31:0] _RAND_58;
  reg [31:0] _RAND_59;
  reg [31:0] _RAND_60;
  reg [31:0] _RAND_61;
  reg [31:0] _RAND_62;
  reg [31:0] _RAND_63;
  reg [31:0] _RAND_64;
  reg [31:0] _RAND_65;
  reg [31:0] _RAND_66;
  reg [31:0] _RAND_67;
  reg [31:0] _RAND_68;
  reg [31:0] _RAND_69;
  reg [31:0] _RAND_70;
  reg [31:0] _RAND_71;
  reg [31:0] _RAND_72;
  reg [31:0] _RAND_73;
  reg [31:0] _RAND_74;
  reg [31:0] _RAND_75;
  reg [31:0] _RAND_76;
  reg [31:0] _RAND_77;
  reg [31:0] _RAND_78;
  reg [31:0] _RAND_79;
  reg [31:0] _RAND_80;
  reg [31:0] _RAND_81;
  reg [31:0] _RAND_82;
  reg [31:0] _RAND_83;
  reg [31:0] _RAND_84;
  reg [31:0] _RAND_85;
  reg [31:0] _RAND_86;
  reg [31:0] _RAND_87;
  reg [31:0] _RAND_88;
  reg [31:0] _RAND_89;
  reg [31:0] _RAND_90;
  reg [31:0] _RAND_91;
  reg [31:0] _RAND_92;
  reg [31:0] _RAND_93;
  reg [31:0] _RAND_94;
  reg [31:0] _RAND_95;
  reg [31:0] _RAND_96;
  reg [31:0] _RAND_97;
  reg [31:0] _RAND_98;
  reg [31:0] _RAND_99;
  reg [31:0] _RAND_100;
  reg [31:0] _RAND_101;
  reg [31:0] _RAND_102;
  reg [31:0] _RAND_103;
  reg [31:0] _RAND_104;
  reg [31:0] _RAND_105;
  reg [31:0] _RAND_106;
`endif // RANDOMIZE_REG_INIT
  wire  ibuf_clock; // @[RocketCore.scala 264:20]
  wire  ibuf_reset; // @[RocketCore.scala 264:20]
  wire  ibuf_io_imem_ready; // @[RocketCore.scala 264:20]
  wire  ibuf_io_imem_valid; // @[RocketCore.scala 264:20]
  wire [31:0] ibuf_io_imem_bits_pc; // @[RocketCore.scala 264:20]
  wire [31:0] ibuf_io_imem_bits_data; // @[RocketCore.scala 264:20]
  wire  ibuf_io_imem_bits_xcpt_ae_inst; // @[RocketCore.scala 264:20]
  wire  ibuf_io_imem_bits_replay; // @[RocketCore.scala 264:20]
  wire  ibuf_io_kill; // @[RocketCore.scala 264:20]
  wire [31:0] ibuf_io_pc; // @[RocketCore.scala 264:20]
  wire  ibuf_io_inst_0_ready; // @[RocketCore.scala 264:20]
  wire  ibuf_io_inst_0_valid; // @[RocketCore.scala 264:20]
  wire  ibuf_io_inst_0_bits_xcpt0_ae_inst; // @[RocketCore.scala 264:20]
  wire  ibuf_io_inst_0_bits_xcpt1_pf_inst; // @[RocketCore.scala 264:20]
  wire  ibuf_io_inst_0_bits_xcpt1_gf_inst; // @[RocketCore.scala 264:20]
  wire  ibuf_io_inst_0_bits_xcpt1_ae_inst; // @[RocketCore.scala 264:20]
  wire  ibuf_io_inst_0_bits_replay; // @[RocketCore.scala 264:20]
  wire  ibuf_io_inst_0_bits_rvc; // @[RocketCore.scala 264:20]
  wire [31:0] ibuf_io_inst_0_bits_inst_bits; // @[RocketCore.scala 264:20]
  wire [4:0] ibuf_io_inst_0_bits_inst_rd; // @[RocketCore.scala 264:20]
  wire [4:0] ibuf_io_inst_0_bits_inst_rs1; // @[RocketCore.scala 264:20]
  wire [4:0] ibuf_io_inst_0_bits_inst_rs2; // @[RocketCore.scala 264:20]
  wire [31:0] ibuf_io_inst_0_bits_raw; // @[RocketCore.scala 264:20]
  reg [31:0] rf [0:30]; // @[RocketCore.scala 1064:15]
  wire  rf_id_rs_MPORT_en; // @[RocketCore.scala 1064:15]
  wire [4:0] rf_id_rs_MPORT_addr; // @[RocketCore.scala 1064:15]
  wire [31:0] rf_id_rs_MPORT_data; // @[RocketCore.scala 1064:15]
  wire  rf_id_rs_MPORT_1_en; // @[RocketCore.scala 1064:15]
  wire [4:0] rf_id_rs_MPORT_1_addr; // @[RocketCore.scala 1064:15]
  wire [31:0] rf_id_rs_MPORT_1_data; // @[RocketCore.scala 1064:15]
  wire [31:0] rf_MPORT_data; // @[RocketCore.scala 1064:15]
  wire [4:0] rf_MPORT_addr; // @[RocketCore.scala 1064:15]
  wire  rf_MPORT_mask; // @[RocketCore.scala 1064:15]
  wire  rf_MPORT_en; // @[RocketCore.scala 1064:15]
  wire  csr_clock; // @[RocketCore.scala 293:19]
  wire  csr_reset; // @[RocketCore.scala 293:19]
  wire  csr_io_ungated_clock; // @[RocketCore.scala 293:19]
  wire  csr_io_interrupts_debug; // @[RocketCore.scala 293:19]
  wire  csr_io_interrupts_mtip; // @[RocketCore.scala 293:19]
  wire  csr_io_interrupts_msip; // @[RocketCore.scala 293:19]
  wire  csr_io_interrupts_meip; // @[RocketCore.scala 293:19]
  wire  csr_io_hartid; // @[RocketCore.scala 293:19]
  wire [11:0] csr_io_rw_addr; // @[RocketCore.scala 293:19]
  wire [2:0] csr_io_rw_cmd; // @[RocketCore.scala 293:19]
  wire [31:0] csr_io_rw_rdata; // @[RocketCore.scala 293:19]
  wire [31:0] csr_io_rw_wdata; // @[RocketCore.scala 293:19]
  wire [31:0] csr_io_decode_0_inst; // @[RocketCore.scala 293:19]
  wire  csr_io_decode_0_fp_illegal; // @[RocketCore.scala 293:19]
  wire  csr_io_decode_0_fp_csr; // @[RocketCore.scala 293:19]
  wire  csr_io_decode_0_rocc_illegal; // @[RocketCore.scala 293:19]
  wire  csr_io_decode_0_read_illegal; // @[RocketCore.scala 293:19]
  wire  csr_io_decode_0_write_illegal; // @[RocketCore.scala 293:19]
  wire  csr_io_decode_0_write_flush; // @[RocketCore.scala 293:19]
  wire  csr_io_decode_0_system_illegal; // @[RocketCore.scala 293:19]
  wire  csr_io_csr_stall; // @[RocketCore.scala 293:19]
  wire  csr_io_eret; // @[RocketCore.scala 293:19]
  wire  csr_io_singleStep; // @[RocketCore.scala 293:19]
  wire  csr_io_status_debug; // @[RocketCore.scala 293:19]
  wire  csr_io_status_cease; // @[RocketCore.scala 293:19]
  wire  csr_io_status_wfi; // @[RocketCore.scala 293:19]
  wire [31:0] csr_io_status_isa; // @[RocketCore.scala 293:19]
  wire [1:0] csr_io_status_dprv; // @[RocketCore.scala 293:19]
  wire  csr_io_status_dv; // @[RocketCore.scala 293:19]
  wire [1:0] csr_io_status_prv; // @[RocketCore.scala 293:19]
  wire  csr_io_status_v; // @[RocketCore.scala 293:19]
  wire  csr_io_status_sd; // @[RocketCore.scala 293:19]
  wire [22:0] csr_io_status_zero2; // @[RocketCore.scala 293:19]
  wire  csr_io_status_mpv; // @[RocketCore.scala 293:19]
  wire  csr_io_status_gva; // @[RocketCore.scala 293:19]
  wire  csr_io_status_mbe; // @[RocketCore.scala 293:19]
  wire  csr_io_status_sbe; // @[RocketCore.scala 293:19]
  wire [1:0] csr_io_status_sxl; // @[RocketCore.scala 293:19]
  wire [1:0] csr_io_status_uxl; // @[RocketCore.scala 293:19]
  wire  csr_io_status_sd_rv32; // @[RocketCore.scala 293:19]
  wire [7:0] csr_io_status_zero1; // @[RocketCore.scala 293:19]
  wire  csr_io_status_tsr; // @[RocketCore.scala 293:19]
  wire  csr_io_status_tw; // @[RocketCore.scala 293:19]
  wire  csr_io_status_tvm; // @[RocketCore.scala 293:19]
  wire  csr_io_status_mxr; // @[RocketCore.scala 293:19]
  wire  csr_io_status_sum; // @[RocketCore.scala 293:19]
  wire  csr_io_status_mprv; // @[RocketCore.scala 293:19]
  wire [1:0] csr_io_status_xs; // @[RocketCore.scala 293:19]
  wire [1:0] csr_io_status_fs; // @[RocketCore.scala 293:19]
  wire [1:0] csr_io_status_mpp; // @[RocketCore.scala 293:19]
  wire [1:0] csr_io_status_vs; // @[RocketCore.scala 293:19]
  wire  csr_io_status_spp; // @[RocketCore.scala 293:19]
  wire  csr_io_status_mpie; // @[RocketCore.scala 293:19]
  wire  csr_io_status_ube; // @[RocketCore.scala 293:19]
  wire  csr_io_status_spie; // @[RocketCore.scala 293:19]
  wire  csr_io_status_upie; // @[RocketCore.scala 293:19]
  wire  csr_io_status_mie; // @[RocketCore.scala 293:19]
  wire  csr_io_status_hie; // @[RocketCore.scala 293:19]
  wire  csr_io_status_sie; // @[RocketCore.scala 293:19]
  wire  csr_io_status_uie; // @[RocketCore.scala 293:19]
  wire [31:0] csr_io_evec; // @[RocketCore.scala 293:19]
  wire  csr_io_exception; // @[RocketCore.scala 293:19]
  wire  csr_io_retire; // @[RocketCore.scala 293:19]
  wire [31:0] csr_io_cause; // @[RocketCore.scala 293:19]
  wire [31:0] csr_io_pc; // @[RocketCore.scala 293:19]
  wire [31:0] csr_io_tval; // @[RocketCore.scala 293:19]
  wire  csr_io_gva; // @[RocketCore.scala 293:19]
  wire [31:0] csr_io_time; // @[RocketCore.scala 293:19]
  wire  csr_io_interrupt; // @[RocketCore.scala 293:19]
  wire [31:0] csr_io_interrupt_cause; // @[RocketCore.scala 293:19]
  wire  csr_io_bp_0_control_action; // @[RocketCore.scala 293:19]
  wire [1:0] csr_io_bp_0_control_tmatch; // @[RocketCore.scala 293:19]
  wire  csr_io_bp_0_control_x; // @[RocketCore.scala 293:19]
  wire  csr_io_bp_0_control_w; // @[RocketCore.scala 293:19]
  wire  csr_io_bp_0_control_r; // @[RocketCore.scala 293:19]
  wire [31:0] csr_io_bp_0_address; // @[RocketCore.scala 293:19]
  wire  csr_io_pmp_0_cfg_l; // @[RocketCore.scala 293:19]
  wire [1:0] csr_io_pmp_0_cfg_a; // @[RocketCore.scala 293:19]
  wire  csr_io_pmp_0_cfg_x; // @[RocketCore.scala 293:19]
  wire  csr_io_pmp_0_cfg_w; // @[RocketCore.scala 293:19]
  wire  csr_io_pmp_0_cfg_r; // @[RocketCore.scala 293:19]
  wire [29:0] csr_io_pmp_0_addr; // @[RocketCore.scala 293:19]
  wire [31:0] csr_io_pmp_0_mask; // @[RocketCore.scala 293:19]
  wire  csr_io_pmp_1_cfg_l; // @[RocketCore.scala 293:19]
  wire [1:0] csr_io_pmp_1_cfg_a; // @[RocketCore.scala 293:19]
  wire  csr_io_pmp_1_cfg_x; // @[RocketCore.scala 293:19]
  wire  csr_io_pmp_1_cfg_w; // @[RocketCore.scala 293:19]
  wire  csr_io_pmp_1_cfg_r; // @[RocketCore.scala 293:19]
  wire [29:0] csr_io_pmp_1_addr; // @[RocketCore.scala 293:19]
  wire [31:0] csr_io_pmp_1_mask; // @[RocketCore.scala 293:19]
  wire  csr_io_pmp_2_cfg_l; // @[RocketCore.scala 293:19]
  wire [1:0] csr_io_pmp_2_cfg_a; // @[RocketCore.scala 293:19]
  wire  csr_io_pmp_2_cfg_x; // @[RocketCore.scala 293:19]
  wire  csr_io_pmp_2_cfg_w; // @[RocketCore.scala 293:19]
  wire  csr_io_pmp_2_cfg_r; // @[RocketCore.scala 293:19]
  wire [29:0] csr_io_pmp_2_addr; // @[RocketCore.scala 293:19]
  wire [31:0] csr_io_pmp_2_mask; // @[RocketCore.scala 293:19]
  wire  csr_io_pmp_3_cfg_l; // @[RocketCore.scala 293:19]
  wire [1:0] csr_io_pmp_3_cfg_a; // @[RocketCore.scala 293:19]
  wire  csr_io_pmp_3_cfg_x; // @[RocketCore.scala 293:19]
  wire  csr_io_pmp_3_cfg_w; // @[RocketCore.scala 293:19]
  wire  csr_io_pmp_3_cfg_r; // @[RocketCore.scala 293:19]
  wire [29:0] csr_io_pmp_3_addr; // @[RocketCore.scala 293:19]
  wire [31:0] csr_io_pmp_3_mask; // @[RocketCore.scala 293:19]
  wire  csr_io_pmp_4_cfg_l; // @[RocketCore.scala 293:19]
  wire [1:0] csr_io_pmp_4_cfg_a; // @[RocketCore.scala 293:19]
  wire  csr_io_pmp_4_cfg_x; // @[RocketCore.scala 293:19]
  wire  csr_io_pmp_4_cfg_w; // @[RocketCore.scala 293:19]
  wire  csr_io_pmp_4_cfg_r; // @[RocketCore.scala 293:19]
  wire [29:0] csr_io_pmp_4_addr; // @[RocketCore.scala 293:19]
  wire [31:0] csr_io_pmp_4_mask; // @[RocketCore.scala 293:19]
  wire  csr_io_pmp_5_cfg_l; // @[RocketCore.scala 293:19]
  wire [1:0] csr_io_pmp_5_cfg_a; // @[RocketCore.scala 293:19]
  wire  csr_io_pmp_5_cfg_x; // @[RocketCore.scala 293:19]
  wire  csr_io_pmp_5_cfg_w; // @[RocketCore.scala 293:19]
  wire  csr_io_pmp_5_cfg_r; // @[RocketCore.scala 293:19]
  wire [29:0] csr_io_pmp_5_addr; // @[RocketCore.scala 293:19]
  wire [31:0] csr_io_pmp_5_mask; // @[RocketCore.scala 293:19]
  wire  csr_io_pmp_6_cfg_l; // @[RocketCore.scala 293:19]
  wire [1:0] csr_io_pmp_6_cfg_a; // @[RocketCore.scala 293:19]
  wire  csr_io_pmp_6_cfg_x; // @[RocketCore.scala 293:19]
  wire  csr_io_pmp_6_cfg_w; // @[RocketCore.scala 293:19]
  wire  csr_io_pmp_6_cfg_r; // @[RocketCore.scala 293:19]
  wire [29:0] csr_io_pmp_6_addr; // @[RocketCore.scala 293:19]
  wire [31:0] csr_io_pmp_6_mask; // @[RocketCore.scala 293:19]
  wire  csr_io_pmp_7_cfg_l; // @[RocketCore.scala 293:19]
  wire [1:0] csr_io_pmp_7_cfg_a; // @[RocketCore.scala 293:19]
  wire  csr_io_pmp_7_cfg_x; // @[RocketCore.scala 293:19]
  wire  csr_io_pmp_7_cfg_w; // @[RocketCore.scala 293:19]
  wire  csr_io_pmp_7_cfg_r; // @[RocketCore.scala 293:19]
  wire [29:0] csr_io_pmp_7_addr; // @[RocketCore.scala 293:19]
  wire [31:0] csr_io_pmp_7_mask; // @[RocketCore.scala 293:19]
  wire  csr_io_inhibit_cycle; // @[RocketCore.scala 293:19]
  wire [31:0] csr_io_inst_0; // @[RocketCore.scala 293:19]
  wire  csr_io_trace_0_valid; // @[RocketCore.scala 293:19]
  wire [31:0] csr_io_trace_0_iaddr; // @[RocketCore.scala 293:19]
  wire [31:0] csr_io_trace_0_insn; // @[RocketCore.scala 293:19]
  wire  csr_io_trace_0_exception; // @[RocketCore.scala 293:19]
  wire [31:0] csr_io_customCSRs_0_value; // @[RocketCore.scala 293:19]
  wire  bpu_io_status_debug; // @[RocketCore.scala 336:19]
  wire  bpu_io_bp_0_control_action; // @[RocketCore.scala 336:19]
  wire [1:0] bpu_io_bp_0_control_tmatch; // @[RocketCore.scala 336:19]
  wire  bpu_io_bp_0_control_x; // @[RocketCore.scala 336:19]
  wire  bpu_io_bp_0_control_w; // @[RocketCore.scala 336:19]
  wire  bpu_io_bp_0_control_r; // @[RocketCore.scala 336:19]
  wire [31:0] bpu_io_bp_0_address; // @[RocketCore.scala 336:19]
  wire [31:0] bpu_io_pc; // @[RocketCore.scala 336:19]
  wire [31:0] bpu_io_ea; // @[RocketCore.scala 336:19]
  wire  bpu_io_xcpt_if; // @[RocketCore.scala 336:19]
  wire  bpu_io_xcpt_ld; // @[RocketCore.scala 336:19]
  wire  bpu_io_xcpt_st; // @[RocketCore.scala 336:19]
  wire  bpu_io_debug_if; // @[RocketCore.scala 336:19]
  wire  bpu_io_debug_ld; // @[RocketCore.scala 336:19]
  wire  bpu_io_debug_st; // @[RocketCore.scala 336:19]
  wire [3:0] alu_io_fn; // @[RocketCore.scala 401:19]
  wire [31:0] alu_io_in2; // @[RocketCore.scala 401:19]
  wire [31:0] alu_io_in1; // @[RocketCore.scala 401:19]
  wire [31:0] alu_io_out; // @[RocketCore.scala 401:19]
  wire [31:0] alu_io_adder_out; // @[RocketCore.scala 401:19]
  wire  alu_io_cmp_out; // @[RocketCore.scala 401:19]
  wire  div_clock; // @[RocketCore.scala 425:19]
  wire  div_reset; // @[RocketCore.scala 425:19]
  wire  div_io_req_ready; // @[RocketCore.scala 425:19]
  wire  div_io_req_valid; // @[RocketCore.scala 425:19]
  wire [3:0] div_io_req_bits_fn; // @[RocketCore.scala 425:19]
  wire [31:0] div_io_req_bits_in1; // @[RocketCore.scala 425:19]
  wire [31:0] div_io_req_bits_in2; // @[RocketCore.scala 425:19]
  wire [4:0] div_io_req_bits_tag; // @[RocketCore.scala 425:19]
  wire  div_io_kill; // @[RocketCore.scala 425:19]
  wire  div_io_resp_ready; // @[RocketCore.scala 425:19]
  wire  div_io_resp_valid; // @[RocketCore.scala 425:19]
  wire [31:0] div_io_resp_bits_data; // @[RocketCore.scala 425:19]
  wire [4:0] div_io_resp_bits_tag; // @[RocketCore.scala 425:19]
  wire  PlusArgTimeout_clock; // @[PlusArg.scala 89:11]
  wire  PlusArgTimeout_reset; // @[PlusArg.scala 89:11]
  wire [31:0] PlusArgTimeout_io_count; // @[PlusArg.scala 89:11]
  reg  id_reg_pause; // @[RocketCore.scala 117:25]
  reg  imem_might_request_reg; // @[RocketCore.scala 118:35]
  reg  ex_ctrl_fp; // @[RocketCore.scala 195:20]
  reg  ex_ctrl_rocc; // @[RocketCore.scala 195:20]
  reg  ex_ctrl_branch; // @[RocketCore.scala 195:20]
  reg  ex_ctrl_jal; // @[RocketCore.scala 195:20]
  reg  ex_ctrl_jalr; // @[RocketCore.scala 195:20]
  reg  ex_ctrl_rxs2; // @[RocketCore.scala 195:20]
  reg  ex_ctrl_rxs1; // @[RocketCore.scala 195:20]
  reg [1:0] ex_ctrl_sel_alu2; // @[RocketCore.scala 195:20]
  reg [1:0] ex_ctrl_sel_alu1; // @[RocketCore.scala 195:20]
  reg [2:0] ex_ctrl_sel_imm; // @[RocketCore.scala 195:20]
  reg [3:0] ex_ctrl_alu_fn; // @[RocketCore.scala 195:20]
  reg  ex_ctrl_mem; // @[RocketCore.scala 195:20]
  reg [4:0] ex_ctrl_mem_cmd; // @[RocketCore.scala 195:20]
  reg  ex_ctrl_rfs1; // @[RocketCore.scala 195:20]
  reg  ex_ctrl_rfs2; // @[RocketCore.scala 195:20]
  reg  ex_ctrl_wfd; // @[RocketCore.scala 195:20]
  reg  ex_ctrl_mul; // @[RocketCore.scala 195:20]
  reg  ex_ctrl_div; // @[RocketCore.scala 195:20]
  reg  ex_ctrl_wxd; // @[RocketCore.scala 195:20]
  reg [2:0] ex_ctrl_csr; // @[RocketCore.scala 195:20]
  reg  ex_ctrl_fence_i; // @[RocketCore.scala 195:20]
  reg  mem_ctrl_fp; // @[RocketCore.scala 196:21]
  reg  mem_ctrl_rocc; // @[RocketCore.scala 196:21]
  reg  mem_ctrl_branch; // @[RocketCore.scala 196:21]
  reg  mem_ctrl_jal; // @[RocketCore.scala 196:21]
  reg  mem_ctrl_jalr; // @[RocketCore.scala 196:21]
  reg  mem_ctrl_rxs2; // @[RocketCore.scala 196:21]
  reg  mem_ctrl_rxs1; // @[RocketCore.scala 196:21]
  reg  mem_ctrl_mem; // @[RocketCore.scala 196:21]
  reg  mem_ctrl_rfs1; // @[RocketCore.scala 196:21]
  reg  mem_ctrl_rfs2; // @[RocketCore.scala 196:21]
  reg  mem_ctrl_wfd; // @[RocketCore.scala 196:21]
  reg  mem_ctrl_mul; // @[RocketCore.scala 196:21]
  reg  mem_ctrl_div; // @[RocketCore.scala 196:21]
  reg  mem_ctrl_wxd; // @[RocketCore.scala 196:21]
  reg [2:0] mem_ctrl_csr; // @[RocketCore.scala 196:21]
  reg  mem_ctrl_fence_i; // @[RocketCore.scala 196:21]
  reg  wb_ctrl_rocc; // @[RocketCore.scala 197:20]
  reg  wb_ctrl_rxs2; // @[RocketCore.scala 197:20]
  reg  wb_ctrl_rxs1; // @[RocketCore.scala 197:20]
  reg  wb_ctrl_mem; // @[RocketCore.scala 197:20]
  reg  wb_ctrl_rfs1; // @[RocketCore.scala 197:20]
  reg  wb_ctrl_rfs2; // @[RocketCore.scala 197:20]
  reg  wb_ctrl_wfd; // @[RocketCore.scala 197:20]
  reg  wb_ctrl_div; // @[RocketCore.scala 197:20]
  reg  wb_ctrl_wxd; // @[RocketCore.scala 197:20]
  reg [2:0] wb_ctrl_csr; // @[RocketCore.scala 197:20]
  reg  wb_ctrl_fence_i; // @[RocketCore.scala 197:20]
  reg  ex_reg_xcpt_interrupt; // @[RocketCore.scala 199:35]
  reg  ex_reg_valid; // @[RocketCore.scala 200:35]
  reg  ex_reg_rvc; // @[RocketCore.scala 201:35]
  reg  ex_reg_xcpt; // @[RocketCore.scala 203:35]
  reg  ex_reg_flush_pipe; // @[RocketCore.scala 204:35]
  reg  ex_reg_load_use; // @[RocketCore.scala 205:35]
  reg [31:0] ex_reg_cause; // @[RocketCore.scala 206:35]
  reg  ex_reg_replay; // @[RocketCore.scala 207:26]
  reg [31:0] ex_reg_pc; // @[RocketCore.scala 208:22]
  reg [1:0] ex_reg_mem_size; // @[RocketCore.scala 209:28]
  reg [31:0] ex_reg_inst; // @[RocketCore.scala 211:24]
  reg [31:0] ex_reg_raw_inst; // @[RocketCore.scala 212:28]
  reg  mem_reg_xcpt_interrupt; // @[RocketCore.scala 217:36]
  reg  mem_reg_valid; // @[RocketCore.scala 218:36]
  reg  mem_reg_rvc; // @[RocketCore.scala 219:36]
  reg  mem_reg_xcpt; // @[RocketCore.scala 221:36]
  reg  mem_reg_replay; // @[RocketCore.scala 222:36]
  reg  mem_reg_flush_pipe; // @[RocketCore.scala 223:36]
  reg [31:0] mem_reg_cause; // @[RocketCore.scala 224:36]
  reg  mem_reg_slow_bypass; // @[RocketCore.scala 225:36]
  reg  mem_reg_load; // @[RocketCore.scala 226:36]
  reg  mem_reg_store; // @[RocketCore.scala 227:36]
  reg [31:0] mem_reg_pc; // @[RocketCore.scala 229:23]
  reg [31:0] mem_reg_inst; // @[RocketCore.scala 230:25]
  reg  mem_reg_hls_or_dv; // @[RocketCore.scala 232:30]
  reg [31:0] mem_reg_raw_inst; // @[RocketCore.scala 233:29]
  reg [31:0] mem_reg_wdata; // @[RocketCore.scala 236:26]
  reg [31:0] mem_reg_rs2; // @[RocketCore.scala 237:24]
  reg  mem_br_taken; // @[RocketCore.scala 238:25]
  reg  wb_reg_valid; // @[RocketCore.scala 242:35]
  reg  wb_reg_xcpt; // @[RocketCore.scala 243:35]
  reg  wb_reg_replay; // @[RocketCore.scala 244:35]
  reg  wb_reg_flush_pipe; // @[RocketCore.scala 245:35]
  reg [31:0] wb_reg_cause; // @[RocketCore.scala 246:35]
  reg [31:0] wb_reg_pc; // @[RocketCore.scala 248:22]
  reg  wb_reg_hls_or_dv; // @[RocketCore.scala 250:29]
  reg [31:0] wb_reg_inst; // @[RocketCore.scala 253:24]
  reg [31:0] wb_reg_raw_inst; // @[RocketCore.scala 254:28]
  reg [31:0] wb_reg_wdata; // @[RocketCore.scala 255:25]
  wire  replay_wb_common = io_dmem_s2_nack | wb_reg_replay; // @[RocketCore.scala 666:42]
  wire  replay_wb_rocc = wb_reg_valid & wb_ctrl_rocc; // @[RocketCore.scala 667:37]
  wire  replay_wb = replay_wb_common | replay_wb_rocc; // @[RocketCore.scala 668:36]
  wire  _T_90 = wb_reg_valid & wb_ctrl_mem; // @[RocketCore.scala 639:19]
  wire  _T_91 = wb_reg_valid & wb_ctrl_mem & io_dmem_s2_xcpt_pf_st; // @[RocketCore.scala 639:34]
  wire  _T_93 = _T_90 & io_dmem_s2_xcpt_pf_ld; // @[RocketCore.scala 640:34]
  wire  _T_99 = _T_90 & io_dmem_s2_xcpt_ae_st; // @[RocketCore.scala 643:34]
  wire  _T_101 = _T_90 & io_dmem_s2_xcpt_ae_ld; // @[RocketCore.scala 644:34]
  wire  _T_103 = _T_90 & io_dmem_s2_xcpt_ma_st; // @[RocketCore.scala 645:34]
  wire  _T_105 = _T_90 & io_dmem_s2_xcpt_ma_ld; // @[RocketCore.scala 646:34]
  wire  wb_xcpt = wb_reg_xcpt | _T_91 | _T_93 | _T_99 | _T_101 | _T_103 | _T_105; // @[RocketCore.scala 1024:26]
  wire  take_pc_wb = replay_wb | wb_xcpt | csr_io_eret | wb_reg_flush_pipe; // @[RocketCore.scala 669:53]
  wire  _take_pc_mem_T = ~mem_reg_xcpt; // @[RocketCore.scala 543:35]
  wire  _mem_cfi_taken_T = mem_ctrl_branch & mem_br_taken; // @[RocketCore.scala 540:40]
  wire  mem_cfi_taken = mem_ctrl_branch & mem_br_taken | mem_ctrl_jalr | mem_ctrl_jal; // @[RocketCore.scala 540:74]
  wire  take_pc_mem = mem_reg_valid & ~mem_reg_xcpt & mem_cfi_taken; // @[RocketCore.scala 543:49]
  wire  take_pc_mem_wb = take_pc_wb | take_pc_mem; // @[RocketCore.scala 260:35]
  wire [31:0] id_ctrl_decoder_decoded_plaInput = ibuf_io_inst_0_bits_inst_bits; // @[decoder.scala 38:16 pla.scala 77:22]
  wire [31:0] id_ctrl_decoder_decoded_invInputs = ~id_ctrl_decoder_decoded_plaInput; // @[pla.scala 78:21]
  wire  id_ctrl_decoder_decoded_andMatrixInput_0 = id_ctrl_decoder_decoded_plaInput[0]; // @[pla.scala 90:45]
  wire  id_ctrl_decoder_decoded_andMatrixInput_1 = id_ctrl_decoder_decoded_plaInput[1]; // @[pla.scala 90:45]
  wire  id_ctrl_decoder_decoded_andMatrixInput_2 = id_ctrl_decoder_decoded_invInputs[2]; // @[pla.scala 91:29]
  wire  id_ctrl_decoder_decoded_andMatrixInput_3 = id_ctrl_decoder_decoded_invInputs[3]; // @[pla.scala 91:29]
  wire  id_ctrl_decoder_decoded_andMatrixInput_4 = id_ctrl_decoder_decoded_invInputs[4]; // @[pla.scala 91:29]
  wire  id_ctrl_decoder_decoded_andMatrixInput_5 = id_ctrl_decoder_decoded_invInputs[5]; // @[pla.scala 91:29]
  wire  id_ctrl_decoder_decoded_andMatrixInput_6 = id_ctrl_decoder_decoded_invInputs[6]; // @[pla.scala 91:29]
  wire  id_ctrl_decoder_decoded_andMatrixInput_7 = id_ctrl_decoder_decoded_invInputs[13]; // @[pla.scala 91:29]
  wire [7:0] _id_ctrl_decoder_decoded_T = {id_ctrl_decoder_decoded_andMatrixInput_0,
    id_ctrl_decoder_decoded_andMatrixInput_1,id_ctrl_decoder_decoded_andMatrixInput_2,
    id_ctrl_decoder_decoded_andMatrixInput_3,id_ctrl_decoder_decoded_andMatrixInput_4,
    id_ctrl_decoder_decoded_andMatrixInput_5,id_ctrl_decoder_decoded_andMatrixInput_6,
    id_ctrl_decoder_decoded_andMatrixInput_7}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_T_1 = &_id_ctrl_decoder_decoded_T; // @[pla.scala 98:74]
  wire  id_ctrl_decoder_decoded_andMatrixInput_6_1 = id_ctrl_decoder_decoded_invInputs[12]; // @[pla.scala 91:29]
  wire [7:0] _id_ctrl_decoder_decoded_T_2 = {id_ctrl_decoder_decoded_andMatrixInput_0,
    id_ctrl_decoder_decoded_andMatrixInput_1,id_ctrl_decoder_decoded_andMatrixInput_2,
    id_ctrl_decoder_decoded_andMatrixInput_3,id_ctrl_decoder_decoded_andMatrixInput_5,
    id_ctrl_decoder_decoded_andMatrixInput_6,id_ctrl_decoder_decoded_andMatrixInput_6_1,
    id_ctrl_decoder_decoded_andMatrixInput_7}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_T_3 = &_id_ctrl_decoder_decoded_T_2; // @[pla.scala 98:74]
  wire  id_ctrl_decoder_decoded_andMatrixInput_7_2 = id_ctrl_decoder_decoded_invInputs[14]; // @[pla.scala 91:29]
  wire [7:0] _id_ctrl_decoder_decoded_T_4 = {id_ctrl_decoder_decoded_andMatrixInput_0,
    id_ctrl_decoder_decoded_andMatrixInput_1,id_ctrl_decoder_decoded_andMatrixInput_2,
    id_ctrl_decoder_decoded_andMatrixInput_3,id_ctrl_decoder_decoded_andMatrixInput_4,
    id_ctrl_decoder_decoded_andMatrixInput_6,id_ctrl_decoder_decoded_andMatrixInput_6_1,
    id_ctrl_decoder_decoded_andMatrixInput_7_2}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_T_5 = &_id_ctrl_decoder_decoded_T_4; // @[pla.scala 98:74]
  wire [7:0] _id_ctrl_decoder_decoded_T_6 = {id_ctrl_decoder_decoded_andMatrixInput_0,
    id_ctrl_decoder_decoded_andMatrixInput_1,id_ctrl_decoder_decoded_andMatrixInput_2,
    id_ctrl_decoder_decoded_andMatrixInput_3,id_ctrl_decoder_decoded_andMatrixInput_5,
    id_ctrl_decoder_decoded_andMatrixInput_6,id_ctrl_decoder_decoded_andMatrixInput_6_1,
    id_ctrl_decoder_decoded_andMatrixInput_7_2}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_T_7 = &_id_ctrl_decoder_decoded_T_6; // @[pla.scala 98:74]
  wire [7:0] _id_ctrl_decoder_decoded_T_8 = {id_ctrl_decoder_decoded_andMatrixInput_0,
    id_ctrl_decoder_decoded_andMatrixInput_1,id_ctrl_decoder_decoded_andMatrixInput_2,
    id_ctrl_decoder_decoded_andMatrixInput_3,id_ctrl_decoder_decoded_andMatrixInput_4,
    id_ctrl_decoder_decoded_andMatrixInput_6,id_ctrl_decoder_decoded_andMatrixInput_7,
    id_ctrl_decoder_decoded_andMatrixInput_7_2}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_T_9 = &_id_ctrl_decoder_decoded_T_8; // @[pla.scala 98:74]
  wire  id_ctrl_decoder_decoded_andMatrixInput_2_5 = id_ctrl_decoder_decoded_plaInput[2]; // @[pla.scala 90:45]
  wire  id_ctrl_decoder_decoded_andMatrixInput_3_5 = id_ctrl_decoder_decoded_plaInput[3]; // @[pla.scala 90:45]
  wire [8:0] _id_ctrl_decoder_decoded_T_10 = {id_ctrl_decoder_decoded_andMatrixInput_0,
    id_ctrl_decoder_decoded_andMatrixInput_1,id_ctrl_decoder_decoded_andMatrixInput_2_5,
    id_ctrl_decoder_decoded_andMatrixInput_3_5,id_ctrl_decoder_decoded_andMatrixInput_4,
    id_ctrl_decoder_decoded_andMatrixInput_5,id_ctrl_decoder_decoded_andMatrixInput_6,
    id_ctrl_decoder_decoded_andMatrixInput_7,id_ctrl_decoder_decoded_andMatrixInput_7_2}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_T_11 = &_id_ctrl_decoder_decoded_T_10; // @[pla.scala 98:74]
  wire  id_ctrl_decoder_decoded_andMatrixInput_4_6 = id_ctrl_decoder_decoded_plaInput[4]; // @[pla.scala 90:45]
  wire [5:0] _id_ctrl_decoder_decoded_T_12 = {id_ctrl_decoder_decoded_andMatrixInput_0,
    id_ctrl_decoder_decoded_andMatrixInput_1,id_ctrl_decoder_decoded_andMatrixInput_2_5,
    id_ctrl_decoder_decoded_andMatrixInput_3,id_ctrl_decoder_decoded_andMatrixInput_4_6,
    id_ctrl_decoder_decoded_andMatrixInput_6}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_T_13 = &_id_ctrl_decoder_decoded_T_12; // @[pla.scala 98:74]
  wire [6:0] _id_ctrl_decoder_decoded_T_14 = {id_ctrl_decoder_decoded_andMatrixInput_0,
    id_ctrl_decoder_decoded_andMatrixInput_1,id_ctrl_decoder_decoded_andMatrixInput_2_5,
    id_ctrl_decoder_decoded_andMatrixInput_3,id_ctrl_decoder_decoded_andMatrixInput_4_6,
    id_ctrl_decoder_decoded_andMatrixInput_5,id_ctrl_decoder_decoded_andMatrixInput_6}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_T_15 = &_id_ctrl_decoder_decoded_T_14; // @[pla.scala 98:74]
  wire  id_ctrl_decoder_decoded_andMatrixInput_5_8 = id_ctrl_decoder_decoded_plaInput[5]; // @[pla.scala 90:45]
  wire [8:0] _id_ctrl_decoder_decoded_T_16 = {id_ctrl_decoder_decoded_andMatrixInput_0,
    id_ctrl_decoder_decoded_andMatrixInput_1,id_ctrl_decoder_decoded_andMatrixInput_2,
    id_ctrl_decoder_decoded_andMatrixInput_3,id_ctrl_decoder_decoded_andMatrixInput_4,
    id_ctrl_decoder_decoded_andMatrixInput_5_8,id_ctrl_decoder_decoded_andMatrixInput_6,
    id_ctrl_decoder_decoded_andMatrixInput_6_1,id_ctrl_decoder_decoded_andMatrixInput_7_2}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_T_17 = &_id_ctrl_decoder_decoded_T_16; // @[pla.scala 98:74]
  wire [7:0] _id_ctrl_decoder_decoded_T_18 = {id_ctrl_decoder_decoded_andMatrixInput_0,
    id_ctrl_decoder_decoded_andMatrixInput_1,id_ctrl_decoder_decoded_andMatrixInput_2,
    id_ctrl_decoder_decoded_andMatrixInput_3,id_ctrl_decoder_decoded_andMatrixInput_4,
    id_ctrl_decoder_decoded_andMatrixInput_5_8,id_ctrl_decoder_decoded_andMatrixInput_7,
    id_ctrl_decoder_decoded_andMatrixInput_7_2}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_T_19 = &_id_ctrl_decoder_decoded_T_18; // @[pla.scala 98:74]
  wire [8:0] _id_ctrl_decoder_decoded_T_20 = {id_ctrl_decoder_decoded_andMatrixInput_0,
    id_ctrl_decoder_decoded_andMatrixInput_1,id_ctrl_decoder_decoded_andMatrixInput_2,
    id_ctrl_decoder_decoded_andMatrixInput_3,id_ctrl_decoder_decoded_andMatrixInput_4,
    id_ctrl_decoder_decoded_andMatrixInput_5_8,id_ctrl_decoder_decoded_andMatrixInput_6,
    id_ctrl_decoder_decoded_andMatrixInput_7,id_ctrl_decoder_decoded_andMatrixInput_7_2}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_T_21 = &_id_ctrl_decoder_decoded_T_20; // @[pla.scala 98:74]
  wire  id_ctrl_decoder_decoded_andMatrixInput_10 = id_ctrl_decoder_decoded_invInputs[25]; // @[pla.scala 91:29]
  wire  id_ctrl_decoder_decoded_andMatrixInput_11 = id_ctrl_decoder_decoded_invInputs[26]; // @[pla.scala 91:29]
  wire  id_ctrl_decoder_decoded_andMatrixInput_12 = id_ctrl_decoder_decoded_invInputs[27]; // @[pla.scala 91:29]
  wire  id_ctrl_decoder_decoded_andMatrixInput_13 = id_ctrl_decoder_decoded_invInputs[28]; // @[pla.scala 91:29]
  wire  id_ctrl_decoder_decoded_andMatrixInput_14 = id_ctrl_decoder_decoded_invInputs[29]; // @[pla.scala 91:29]
  wire  id_ctrl_decoder_decoded_andMatrixInput_15 = id_ctrl_decoder_decoded_invInputs[31]; // @[pla.scala 91:29]
  wire [7:0] id_ctrl_decoder_decoded_lo_11 = {id_ctrl_decoder_decoded_andMatrixInput_7,
    id_ctrl_decoder_decoded_andMatrixInput_7_2,id_ctrl_decoder_decoded_andMatrixInput_10,
    id_ctrl_decoder_decoded_andMatrixInput_11,id_ctrl_decoder_decoded_andMatrixInput_12,
    id_ctrl_decoder_decoded_andMatrixInput_13,id_ctrl_decoder_decoded_andMatrixInput_14,
    id_ctrl_decoder_decoded_andMatrixInput_15}; // @[Cat.scala 31:58]
  wire [15:0] _id_ctrl_decoder_decoded_T_22 = {id_ctrl_decoder_decoded_andMatrixInput_0,
    id_ctrl_decoder_decoded_andMatrixInput_1,id_ctrl_decoder_decoded_andMatrixInput_2,
    id_ctrl_decoder_decoded_andMatrixInput_3,id_ctrl_decoder_decoded_andMatrixInput_4_6,
    id_ctrl_decoder_decoded_andMatrixInput_5_8,id_ctrl_decoder_decoded_andMatrixInput_6,
    id_ctrl_decoder_decoded_andMatrixInput_6_1,id_ctrl_decoder_decoded_lo_11}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_T_23 = &_id_ctrl_decoder_decoded_T_22; // @[pla.scala 98:74]
  wire  id_ctrl_decoder_decoded_andMatrixInput_11_1 = id_ctrl_decoder_decoded_invInputs[30]; // @[pla.scala 91:29]
  wire [5:0] id_ctrl_decoder_decoded_lo_12 = {id_ctrl_decoder_decoded_andMatrixInput_11,
    id_ctrl_decoder_decoded_andMatrixInput_12,id_ctrl_decoder_decoded_andMatrixInput_13,
    id_ctrl_decoder_decoded_andMatrixInput_14,id_ctrl_decoder_decoded_andMatrixInput_11_1,
    id_ctrl_decoder_decoded_andMatrixInput_15}; // @[Cat.scala 31:58]
  wire [12:0] _id_ctrl_decoder_decoded_T_24 = {id_ctrl_decoder_decoded_andMatrixInput_0,
    id_ctrl_decoder_decoded_andMatrixInput_1,id_ctrl_decoder_decoded_andMatrixInput_2,
    id_ctrl_decoder_decoded_andMatrixInput_3,id_ctrl_decoder_decoded_andMatrixInput_4_6,
    id_ctrl_decoder_decoded_andMatrixInput_5_8,id_ctrl_decoder_decoded_andMatrixInput_6,id_ctrl_decoder_decoded_lo_12}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_T_25 = &_id_ctrl_decoder_decoded_T_24; // @[pla.scala 98:74]
  wire  id_ctrl_decoder_decoded_andMatrixInput_6_12 = id_ctrl_decoder_decoded_plaInput[6]; // @[pla.scala 90:45]
  wire [7:0] _id_ctrl_decoder_decoded_T_26 = {id_ctrl_decoder_decoded_andMatrixInput_0,
    id_ctrl_decoder_decoded_andMatrixInput_1,id_ctrl_decoder_decoded_andMatrixInput_2,
    id_ctrl_decoder_decoded_andMatrixInput_3,id_ctrl_decoder_decoded_andMatrixInput_4,
    id_ctrl_decoder_decoded_andMatrixInput_5_8,id_ctrl_decoder_decoded_andMatrixInput_6_12,
    id_ctrl_decoder_decoded_andMatrixInput_7}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_T_27 = &_id_ctrl_decoder_decoded_T_26; // @[pla.scala 98:74]
  wire [8:0] _id_ctrl_decoder_decoded_T_28 = {id_ctrl_decoder_decoded_andMatrixInput_0,
    id_ctrl_decoder_decoded_andMatrixInput_1,id_ctrl_decoder_decoded_andMatrixInput_2,
    id_ctrl_decoder_decoded_andMatrixInput_3,id_ctrl_decoder_decoded_andMatrixInput_4,
    id_ctrl_decoder_decoded_andMatrixInput_5_8,id_ctrl_decoder_decoded_andMatrixInput_6_12,
    id_ctrl_decoder_decoded_andMatrixInput_7,id_ctrl_decoder_decoded_andMatrixInput_7_2}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_T_29 = &_id_ctrl_decoder_decoded_T_28; // @[pla.scala 98:74]
  wire [8:0] _id_ctrl_decoder_decoded_T_30 = {id_ctrl_decoder_decoded_andMatrixInput_0,
    id_ctrl_decoder_decoded_andMatrixInput_1,id_ctrl_decoder_decoded_andMatrixInput_3,
    id_ctrl_decoder_decoded_andMatrixInput_4,id_ctrl_decoder_decoded_andMatrixInput_5_8,
    id_ctrl_decoder_decoded_andMatrixInput_6_12,id_ctrl_decoder_decoded_andMatrixInput_6_1,
    id_ctrl_decoder_decoded_andMatrixInput_7,id_ctrl_decoder_decoded_andMatrixInput_7_2}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_T_31 = &_id_ctrl_decoder_decoded_T_30; // @[pla.scala 98:74]
  wire [9:0] _id_ctrl_decoder_decoded_T_32 = {id_ctrl_decoder_decoded_andMatrixInput_0,
    id_ctrl_decoder_decoded_andMatrixInput_1,id_ctrl_decoder_decoded_andMatrixInput_2_5,
    id_ctrl_decoder_decoded_andMatrixInput_3,id_ctrl_decoder_decoded_andMatrixInput_4,
    id_ctrl_decoder_decoded_andMatrixInput_5_8,id_ctrl_decoder_decoded_andMatrixInput_6_12,
    id_ctrl_decoder_decoded_andMatrixInput_6_1,id_ctrl_decoder_decoded_andMatrixInput_7,
    id_ctrl_decoder_decoded_andMatrixInput_7_2}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_T_33 = &_id_ctrl_decoder_decoded_T_32; // @[pla.scala 98:74]
  wire [6:0] _id_ctrl_decoder_decoded_T_34 = {id_ctrl_decoder_decoded_andMatrixInput_0,
    id_ctrl_decoder_decoded_andMatrixInput_1,id_ctrl_decoder_decoded_andMatrixInput_2_5,
    id_ctrl_decoder_decoded_andMatrixInput_3_5,id_ctrl_decoder_decoded_andMatrixInput_4,
    id_ctrl_decoder_decoded_andMatrixInput_5_8,id_ctrl_decoder_decoded_andMatrixInput_6_12}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_T_35 = &_id_ctrl_decoder_decoded_T_34; // @[pla.scala 98:74]
  wire  id_ctrl_decoder_decoded_andMatrixInput_4_18 = id_ctrl_decoder_decoded_invInputs[7]; // @[pla.scala 91:29]
  wire  id_ctrl_decoder_decoded_andMatrixInput_5_18 = id_ctrl_decoder_decoded_invInputs[8]; // @[pla.scala 91:29]
  wire  id_ctrl_decoder_decoded_andMatrixInput_6_17 = id_ctrl_decoder_decoded_invInputs[9]; // @[pla.scala 91:29]
  wire  id_ctrl_decoder_decoded_andMatrixInput_7_15 = id_ctrl_decoder_decoded_invInputs[10]; // @[pla.scala 91:29]
  wire  id_ctrl_decoder_decoded_andMatrixInput_8_8 = id_ctrl_decoder_decoded_invInputs[11]; // @[pla.scala 91:29]
  wire  id_ctrl_decoder_decoded_andMatrixInput_12_2 = id_ctrl_decoder_decoded_invInputs[15]; // @[pla.scala 91:29]
  wire  id_ctrl_decoder_decoded_andMatrixInput_13_1 = id_ctrl_decoder_decoded_invInputs[16]; // @[pla.scala 91:29]
  wire  id_ctrl_decoder_decoded_andMatrixInput_14_1 = id_ctrl_decoder_decoded_invInputs[17]; // @[pla.scala 91:29]
  wire  id_ctrl_decoder_decoded_andMatrixInput_15_1 = id_ctrl_decoder_decoded_invInputs[18]; // @[pla.scala 91:29]
  wire  id_ctrl_decoder_decoded_andMatrixInput_16 = id_ctrl_decoder_decoded_invInputs[19]; // @[pla.scala 91:29]
  wire  id_ctrl_decoder_decoded_andMatrixInput_17 = id_ctrl_decoder_decoded_invInputs[21]; // @[pla.scala 91:29]
  wire  id_ctrl_decoder_decoded_andMatrixInput_18 = id_ctrl_decoder_decoded_invInputs[22]; // @[pla.scala 91:29]
  wire  id_ctrl_decoder_decoded_andMatrixInput_19 = id_ctrl_decoder_decoded_invInputs[23]; // @[pla.scala 91:29]
  wire  id_ctrl_decoder_decoded_andMatrixInput_20 = id_ctrl_decoder_decoded_invInputs[24]; // @[pla.scala 91:29]
  wire [6:0] id_ctrl_decoder_decoded_lo_lo_15 = {id_ctrl_decoder_decoded_andMatrixInput_10,
    id_ctrl_decoder_decoded_andMatrixInput_11,id_ctrl_decoder_decoded_andMatrixInput_12,
    id_ctrl_decoder_decoded_andMatrixInput_13,id_ctrl_decoder_decoded_andMatrixInput_14,
    id_ctrl_decoder_decoded_andMatrixInput_11_1,id_ctrl_decoder_decoded_andMatrixInput_15}; // @[Cat.scala 31:58]
  wire [13:0] id_ctrl_decoder_decoded_lo_18 = {id_ctrl_decoder_decoded_andMatrixInput_14_1,
    id_ctrl_decoder_decoded_andMatrixInput_15_1,id_ctrl_decoder_decoded_andMatrixInput_16,
    id_ctrl_decoder_decoded_andMatrixInput_17,id_ctrl_decoder_decoded_andMatrixInput_18,
    id_ctrl_decoder_decoded_andMatrixInput_19,id_ctrl_decoder_decoded_andMatrixInput_20,id_ctrl_decoder_decoded_lo_lo_15
    }; // @[Cat.scala 31:58]
  wire [6:0] id_ctrl_decoder_decoded_hi_lo_17 = {id_ctrl_decoder_decoded_andMatrixInput_7_15,
    id_ctrl_decoder_decoded_andMatrixInput_8_8,id_ctrl_decoder_decoded_andMatrixInput_6_1,
    id_ctrl_decoder_decoded_andMatrixInput_7,id_ctrl_decoder_decoded_andMatrixInput_7_2,
    id_ctrl_decoder_decoded_andMatrixInput_12_2,id_ctrl_decoder_decoded_andMatrixInput_13_1}; // @[Cat.scala 31:58]
  wire [27:0] _id_ctrl_decoder_decoded_T_36 = {id_ctrl_decoder_decoded_andMatrixInput_0,
    id_ctrl_decoder_decoded_andMatrixInput_4_6,id_ctrl_decoder_decoded_andMatrixInput_5_8,
    id_ctrl_decoder_decoded_andMatrixInput_6_12,id_ctrl_decoder_decoded_andMatrixInput_4_18,
    id_ctrl_decoder_decoded_andMatrixInput_5_18,id_ctrl_decoder_decoded_andMatrixInput_6_17,
    id_ctrl_decoder_decoded_hi_lo_17,id_ctrl_decoder_decoded_lo_18}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_T_37 = &_id_ctrl_decoder_decoded_T_36; // @[pla.scala 98:74]
  wire [14:0] id_ctrl_decoder_decoded_lo_19 = {id_ctrl_decoder_decoded_andMatrixInput_13_1,
    id_ctrl_decoder_decoded_andMatrixInput_14_1,id_ctrl_decoder_decoded_andMatrixInput_15_1,
    id_ctrl_decoder_decoded_andMatrixInput_16,id_ctrl_decoder_decoded_andMatrixInput_17,
    id_ctrl_decoder_decoded_andMatrixInput_18,id_ctrl_decoder_decoded_andMatrixInput_19,
    id_ctrl_decoder_decoded_andMatrixInput_20,id_ctrl_decoder_decoded_lo_lo_15}; // @[Cat.scala 31:58]
  wire [7:0] id_ctrl_decoder_decoded_hi_lo_18 = {id_ctrl_decoder_decoded_andMatrixInput_5_18,
    id_ctrl_decoder_decoded_andMatrixInput_6_17,id_ctrl_decoder_decoded_andMatrixInput_7_15,
    id_ctrl_decoder_decoded_andMatrixInput_8_8,id_ctrl_decoder_decoded_andMatrixInput_6_1,
    id_ctrl_decoder_decoded_andMatrixInput_7,id_ctrl_decoder_decoded_andMatrixInput_7_2,
    id_ctrl_decoder_decoded_andMatrixInput_12_2}; // @[Cat.scala 31:58]
  wire [30:0] _id_ctrl_decoder_decoded_T_38 = {id_ctrl_decoder_decoded_andMatrixInput_0,
    id_ctrl_decoder_decoded_andMatrixInput_1,id_ctrl_decoder_decoded_andMatrixInput_2,
    id_ctrl_decoder_decoded_andMatrixInput_3,id_ctrl_decoder_decoded_andMatrixInput_4_6,
    id_ctrl_decoder_decoded_andMatrixInput_5_8,id_ctrl_decoder_decoded_andMatrixInput_6_12,
    id_ctrl_decoder_decoded_andMatrixInput_4_18,id_ctrl_decoder_decoded_hi_lo_18,id_ctrl_decoder_decoded_lo_19}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_T_39 = &_id_ctrl_decoder_decoded_T_38; // @[pla.scala 98:74]
  wire  id_ctrl_decoder_decoded_andMatrixInput_7_17 = id_ctrl_decoder_decoded_plaInput[12]; // @[pla.scala 90:45]
  wire [9:0] _id_ctrl_decoder_decoded_T_40 = {id_ctrl_decoder_decoded_andMatrixInput_0,
    id_ctrl_decoder_decoded_andMatrixInput_1,id_ctrl_decoder_decoded_andMatrixInput_2_5,
    id_ctrl_decoder_decoded_andMatrixInput_3_5,id_ctrl_decoder_decoded_andMatrixInput_4,
    id_ctrl_decoder_decoded_andMatrixInput_5,id_ctrl_decoder_decoded_andMatrixInput_6,
    id_ctrl_decoder_decoded_andMatrixInput_7_17,id_ctrl_decoder_decoded_andMatrixInput_7,
    id_ctrl_decoder_decoded_andMatrixInput_7_2}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_T_41 = &_id_ctrl_decoder_decoded_T_40; // @[pla.scala 98:74]
  wire [14:0] _id_ctrl_decoder_decoded_T_42 = {id_ctrl_decoder_decoded_andMatrixInput_0,
    id_ctrl_decoder_decoded_andMatrixInput_1,id_ctrl_decoder_decoded_andMatrixInput_2,
    id_ctrl_decoder_decoded_andMatrixInput_3,id_ctrl_decoder_decoded_andMatrixInput_4_6,
    id_ctrl_decoder_decoded_andMatrixInput_6,id_ctrl_decoder_decoded_andMatrixInput_7_17,
    id_ctrl_decoder_decoded_andMatrixInput_7,id_ctrl_decoder_decoded_lo_lo_15}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_T_43 = &_id_ctrl_decoder_decoded_T_42; // @[pla.scala 98:74]
  wire [7:0] id_ctrl_decoder_decoded_lo_22 = {id_ctrl_decoder_decoded_andMatrixInput_7,
    id_ctrl_decoder_decoded_andMatrixInput_10,id_ctrl_decoder_decoded_andMatrixInput_11,
    id_ctrl_decoder_decoded_andMatrixInput_12,id_ctrl_decoder_decoded_andMatrixInput_13,
    id_ctrl_decoder_decoded_andMatrixInput_14,id_ctrl_decoder_decoded_andMatrixInput_11_1,
    id_ctrl_decoder_decoded_andMatrixInput_15}; // @[Cat.scala 31:58]
  wire [15:0] _id_ctrl_decoder_decoded_T_44 = {id_ctrl_decoder_decoded_andMatrixInput_0,
    id_ctrl_decoder_decoded_andMatrixInput_1,id_ctrl_decoder_decoded_andMatrixInput_2,
    id_ctrl_decoder_decoded_andMatrixInput_3,id_ctrl_decoder_decoded_andMatrixInput_4_6,
    id_ctrl_decoder_decoded_andMatrixInput_5,id_ctrl_decoder_decoded_andMatrixInput_6,
    id_ctrl_decoder_decoded_andMatrixInput_7_17,id_ctrl_decoder_decoded_lo_22}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_T_45 = &_id_ctrl_decoder_decoded_T_44; // @[pla.scala 98:74]
  wire [7:0] _id_ctrl_decoder_decoded_T_46 = {id_ctrl_decoder_decoded_andMatrixInput_0,
    id_ctrl_decoder_decoded_andMatrixInput_1,id_ctrl_decoder_decoded_andMatrixInput_2,
    id_ctrl_decoder_decoded_andMatrixInput_3,id_ctrl_decoder_decoded_andMatrixInput_5_8,
    id_ctrl_decoder_decoded_andMatrixInput_6_12,id_ctrl_decoder_decoded_andMatrixInput_7_17,
    id_ctrl_decoder_decoded_andMatrixInput_7}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_T_47 = &_id_ctrl_decoder_decoded_T_46; // @[pla.scala 98:74]
  wire [8:0] _id_ctrl_decoder_decoded_T_48 = {id_ctrl_decoder_decoded_andMatrixInput_0,
    id_ctrl_decoder_decoded_andMatrixInput_1,id_ctrl_decoder_decoded_andMatrixInput_2,
    id_ctrl_decoder_decoded_andMatrixInput_3,id_ctrl_decoder_decoded_andMatrixInput_4,
    id_ctrl_decoder_decoded_andMatrixInput_5_8,id_ctrl_decoder_decoded_andMatrixInput_6_12,
    id_ctrl_decoder_decoded_andMatrixInput_7_17,id_ctrl_decoder_decoded_andMatrixInput_7}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_T_49 = &_id_ctrl_decoder_decoded_T_48; // @[pla.scala 98:74]
  wire [8:0] _id_ctrl_decoder_decoded_T_50 = {id_ctrl_decoder_decoded_andMatrixInput_0,
    id_ctrl_decoder_decoded_andMatrixInput_1,id_ctrl_decoder_decoded_andMatrixInput_2,
    id_ctrl_decoder_decoded_andMatrixInput_3,id_ctrl_decoder_decoded_andMatrixInput_5_8,
    id_ctrl_decoder_decoded_andMatrixInput_6_12,id_ctrl_decoder_decoded_andMatrixInput_7_17,
    id_ctrl_decoder_decoded_andMatrixInput_7,id_ctrl_decoder_decoded_andMatrixInput_7_2}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_T_51 = &_id_ctrl_decoder_decoded_T_50; // @[pla.scala 98:74]
  wire [7:0] _id_ctrl_decoder_decoded_T_52 = {id_ctrl_decoder_decoded_andMatrixInput_0,
    id_ctrl_decoder_decoded_andMatrixInput_1,id_ctrl_decoder_decoded_andMatrixInput_2,
    id_ctrl_decoder_decoded_andMatrixInput_3,id_ctrl_decoder_decoded_andMatrixInput_4_6,
    id_ctrl_decoder_decoded_andMatrixInput_5_8,id_ctrl_decoder_decoded_andMatrixInput_6_12,
    id_ctrl_decoder_decoded_andMatrixInput_7_17}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_T_53 = &_id_ctrl_decoder_decoded_T_52; // @[pla.scala 98:74]
  wire  id_ctrl_decoder_decoded_andMatrixInput_7_24 = id_ctrl_decoder_decoded_plaInput[13]; // @[pla.scala 90:45]
  wire [7:0] _id_ctrl_decoder_decoded_T_54 = {id_ctrl_decoder_decoded_andMatrixInput_0,
    id_ctrl_decoder_decoded_andMatrixInput_1,id_ctrl_decoder_decoded_andMatrixInput_2,
    id_ctrl_decoder_decoded_andMatrixInput_3,id_ctrl_decoder_decoded_andMatrixInput_4_6,
    id_ctrl_decoder_decoded_andMatrixInput_5,id_ctrl_decoder_decoded_andMatrixInput_6,
    id_ctrl_decoder_decoded_andMatrixInput_7_24}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_T_55 = &_id_ctrl_decoder_decoded_T_54; // @[pla.scala 98:74]
  wire [8:0] _id_ctrl_decoder_decoded_T_56 = {id_ctrl_decoder_decoded_andMatrixInput_0,
    id_ctrl_decoder_decoded_andMatrixInput_1,id_ctrl_decoder_decoded_andMatrixInput_2,
    id_ctrl_decoder_decoded_andMatrixInput_3,id_ctrl_decoder_decoded_andMatrixInput_4_6,
    id_ctrl_decoder_decoded_andMatrixInput_5,id_ctrl_decoder_decoded_andMatrixInput_6,
    id_ctrl_decoder_decoded_andMatrixInput_7_24,id_ctrl_decoder_decoded_andMatrixInput_7_2}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_T_57 = &_id_ctrl_decoder_decoded_T_56; // @[pla.scala 98:74]
  wire [5:0] id_ctrl_decoder_decoded_lo_29 = {id_ctrl_decoder_decoded_andMatrixInput_6,
    id_ctrl_decoder_decoded_andMatrixInput_6_1,id_ctrl_decoder_decoded_andMatrixInput_7_24,
    id_ctrl_decoder_decoded_andMatrixInput_7_2,id_ctrl_decoder_decoded_andMatrixInput_12,
    id_ctrl_decoder_decoded_andMatrixInput_13}; // @[Cat.scala 31:58]
  wire [11:0] _id_ctrl_decoder_decoded_T_58 = {id_ctrl_decoder_decoded_andMatrixInput_0,
    id_ctrl_decoder_decoded_andMatrixInput_1,id_ctrl_decoder_decoded_andMatrixInput_2_5,
    id_ctrl_decoder_decoded_andMatrixInput_3_5,id_ctrl_decoder_decoded_andMatrixInput_4,
    id_ctrl_decoder_decoded_andMatrixInput_5_8,id_ctrl_decoder_decoded_lo_29}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_T_59 = &_id_ctrl_decoder_decoded_T_58; // @[pla.scala 98:74]
  wire [14:0] _id_ctrl_decoder_decoded_T_60 = {id_ctrl_decoder_decoded_andMatrixInput_0,
    id_ctrl_decoder_decoded_andMatrixInput_1,id_ctrl_decoder_decoded_andMatrixInput_2,
    id_ctrl_decoder_decoded_andMatrixInput_3,id_ctrl_decoder_decoded_andMatrixInput_4_6,
    id_ctrl_decoder_decoded_andMatrixInput_5_8,id_ctrl_decoder_decoded_andMatrixInput_6,
    id_ctrl_decoder_decoded_andMatrixInput_7_24,id_ctrl_decoder_decoded_lo_lo_15}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_T_61 = &_id_ctrl_decoder_decoded_T_60; // @[pla.scala 98:74]
  wire [7:0] id_ctrl_decoder_decoded_lo_31 = {id_ctrl_decoder_decoded_andMatrixInput_7_2,
    id_ctrl_decoder_decoded_andMatrixInput_10,id_ctrl_decoder_decoded_andMatrixInput_11,
    id_ctrl_decoder_decoded_andMatrixInput_12,id_ctrl_decoder_decoded_andMatrixInput_13,
    id_ctrl_decoder_decoded_andMatrixInput_14,id_ctrl_decoder_decoded_andMatrixInput_11_1,
    id_ctrl_decoder_decoded_andMatrixInput_15}; // @[Cat.scala 31:58]
  wire [15:0] _id_ctrl_decoder_decoded_T_62 = {id_ctrl_decoder_decoded_andMatrixInput_0,
    id_ctrl_decoder_decoded_andMatrixInput_1,id_ctrl_decoder_decoded_andMatrixInput_2,
    id_ctrl_decoder_decoded_andMatrixInput_3,id_ctrl_decoder_decoded_andMatrixInput_4_6,
    id_ctrl_decoder_decoded_andMatrixInput_5_8,id_ctrl_decoder_decoded_andMatrixInput_6,
    id_ctrl_decoder_decoded_andMatrixInput_7_24,id_ctrl_decoder_decoded_lo_31}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_T_63 = &_id_ctrl_decoder_decoded_T_62; // @[pla.scala 98:74]
  wire [7:0] _id_ctrl_decoder_decoded_T_64 = {id_ctrl_decoder_decoded_andMatrixInput_0,
    id_ctrl_decoder_decoded_andMatrixInput_1,id_ctrl_decoder_decoded_andMatrixInput_2,
    id_ctrl_decoder_decoded_andMatrixInput_3,id_ctrl_decoder_decoded_andMatrixInput_4_6,
    id_ctrl_decoder_decoded_andMatrixInput_5_8,id_ctrl_decoder_decoded_andMatrixInput_6_12,
    id_ctrl_decoder_decoded_andMatrixInput_7_24}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_T_65 = &_id_ctrl_decoder_decoded_T_64; // @[pla.scala 98:74]
  wire [8:0] _id_ctrl_decoder_decoded_T_66 = {id_ctrl_decoder_decoded_andMatrixInput_0,
    id_ctrl_decoder_decoded_andMatrixInput_1,id_ctrl_decoder_decoded_andMatrixInput_2,
    id_ctrl_decoder_decoded_andMatrixInput_3,id_ctrl_decoder_decoded_andMatrixInput_4_6,
    id_ctrl_decoder_decoded_andMatrixInput_5_8,id_ctrl_decoder_decoded_andMatrixInput_6_12,
    id_ctrl_decoder_decoded_andMatrixInput_7_24,id_ctrl_decoder_decoded_andMatrixInput_7_2}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_T_67 = &_id_ctrl_decoder_decoded_T_66; // @[pla.scala 98:74]
  wire [8:0] _id_ctrl_decoder_decoded_T_68 = {id_ctrl_decoder_decoded_andMatrixInput_0,
    id_ctrl_decoder_decoded_andMatrixInput_1,id_ctrl_decoder_decoded_andMatrixInput_2,
    id_ctrl_decoder_decoded_andMatrixInput_3,id_ctrl_decoder_decoded_andMatrixInput_4_6,
    id_ctrl_decoder_decoded_andMatrixInput_5,id_ctrl_decoder_decoded_andMatrixInput_6,
    id_ctrl_decoder_decoded_andMatrixInput_7_17,id_ctrl_decoder_decoded_andMatrixInput_7_24}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_T_69 = &_id_ctrl_decoder_decoded_T_68; // @[pla.scala 98:74]
  wire [6:0] id_ctrl_decoder_decoded_lo_35 = {id_ctrl_decoder_decoded_andMatrixInput_7_24,
    id_ctrl_decoder_decoded_andMatrixInput_11,id_ctrl_decoder_decoded_andMatrixInput_12,
    id_ctrl_decoder_decoded_andMatrixInput_13,id_ctrl_decoder_decoded_andMatrixInput_14,
    id_ctrl_decoder_decoded_andMatrixInput_11_1,id_ctrl_decoder_decoded_andMatrixInput_15}; // @[Cat.scala 31:58]
  wire [14:0] _id_ctrl_decoder_decoded_T_70 = {id_ctrl_decoder_decoded_andMatrixInput_0,
    id_ctrl_decoder_decoded_andMatrixInput_1,id_ctrl_decoder_decoded_andMatrixInput_2,
    id_ctrl_decoder_decoded_andMatrixInput_3,id_ctrl_decoder_decoded_andMatrixInput_4_6,
    id_ctrl_decoder_decoded_andMatrixInput_5_8,id_ctrl_decoder_decoded_andMatrixInput_6,
    id_ctrl_decoder_decoded_andMatrixInput_7_17,id_ctrl_decoder_decoded_lo_35}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_T_71 = &_id_ctrl_decoder_decoded_T_70; // @[pla.scala 98:74]
  wire  id_ctrl_decoder_decoded_andMatrixInput_8_22 = id_ctrl_decoder_decoded_plaInput[14]; // @[pla.scala 90:45]
  wire [8:0] _id_ctrl_decoder_decoded_T_72 = {id_ctrl_decoder_decoded_andMatrixInput_0,
    id_ctrl_decoder_decoded_andMatrixInput_1,id_ctrl_decoder_decoded_andMatrixInput_2,
    id_ctrl_decoder_decoded_andMatrixInput_3,id_ctrl_decoder_decoded_andMatrixInput_4_6,
    id_ctrl_decoder_decoded_andMatrixInput_5,id_ctrl_decoder_decoded_andMatrixInput_6,
    id_ctrl_decoder_decoded_andMatrixInput_6_1,id_ctrl_decoder_decoded_andMatrixInput_8_22}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_T_73 = &_id_ctrl_decoder_decoded_T_72; // @[pla.scala 98:74]
  wire [6:0] id_ctrl_decoder_decoded_lo_37 = {id_ctrl_decoder_decoded_andMatrixInput_8_22,
    id_ctrl_decoder_decoded_andMatrixInput_11,id_ctrl_decoder_decoded_andMatrixInput_12,
    id_ctrl_decoder_decoded_andMatrixInput_13,id_ctrl_decoder_decoded_andMatrixInput_14,
    id_ctrl_decoder_decoded_andMatrixInput_11_1,id_ctrl_decoder_decoded_andMatrixInput_15}; // @[Cat.scala 31:58]
  wire [13:0] _id_ctrl_decoder_decoded_T_74 = {id_ctrl_decoder_decoded_andMatrixInput_0,
    id_ctrl_decoder_decoded_andMatrixInput_1,id_ctrl_decoder_decoded_andMatrixInput_2,
    id_ctrl_decoder_decoded_andMatrixInput_3,id_ctrl_decoder_decoded_andMatrixInput_4_6,
    id_ctrl_decoder_decoded_andMatrixInput_5_8,id_ctrl_decoder_decoded_andMatrixInput_6,id_ctrl_decoder_decoded_lo_37}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_T_75 = &_id_ctrl_decoder_decoded_T_74; // @[pla.scala 98:74]
  wire [7:0] _id_ctrl_decoder_decoded_T_76 = {id_ctrl_decoder_decoded_andMatrixInput_0,
    id_ctrl_decoder_decoded_andMatrixInput_1,id_ctrl_decoder_decoded_andMatrixInput_2,
    id_ctrl_decoder_decoded_andMatrixInput_3,id_ctrl_decoder_decoded_andMatrixInput_4,
    id_ctrl_decoder_decoded_andMatrixInput_5_8,id_ctrl_decoder_decoded_andMatrixInput_6_12,
    id_ctrl_decoder_decoded_andMatrixInput_8_22}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_T_77 = &_id_ctrl_decoder_decoded_T_76; // @[pla.scala 98:74]
  wire [6:0] id_ctrl_decoder_decoded_lo_39 = {id_ctrl_decoder_decoded_andMatrixInput_8_22,
    id_ctrl_decoder_decoded_andMatrixInput_10,id_ctrl_decoder_decoded_andMatrixInput_11,
    id_ctrl_decoder_decoded_andMatrixInput_12,id_ctrl_decoder_decoded_andMatrixInput_13,
    id_ctrl_decoder_decoded_andMatrixInput_14,id_ctrl_decoder_decoded_andMatrixInput_15}; // @[Cat.scala 31:58]
  wire [14:0] _id_ctrl_decoder_decoded_T_78 = {id_ctrl_decoder_decoded_andMatrixInput_0,
    id_ctrl_decoder_decoded_andMatrixInput_1,id_ctrl_decoder_decoded_andMatrixInput_2,
    id_ctrl_decoder_decoded_andMatrixInput_3,id_ctrl_decoder_decoded_andMatrixInput_4_6,
    id_ctrl_decoder_decoded_andMatrixInput_6,id_ctrl_decoder_decoded_andMatrixInput_7_17,
    id_ctrl_decoder_decoded_andMatrixInput_7,id_ctrl_decoder_decoded_lo_39}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_T_79 = &_id_ctrl_decoder_decoded_T_78; // @[pla.scala 98:74]
  wire [7:0] id_ctrl_decoder_decoded_lo_40 = {id_ctrl_decoder_decoded_andMatrixInput_7,
    id_ctrl_decoder_decoded_andMatrixInput_8_22,id_ctrl_decoder_decoded_andMatrixInput_10,
    id_ctrl_decoder_decoded_andMatrixInput_11,id_ctrl_decoder_decoded_andMatrixInput_12,
    id_ctrl_decoder_decoded_andMatrixInput_13,id_ctrl_decoder_decoded_andMatrixInput_14,
    id_ctrl_decoder_decoded_andMatrixInput_15}; // @[Cat.scala 31:58]
  wire [15:0] _id_ctrl_decoder_decoded_T_80 = {id_ctrl_decoder_decoded_andMatrixInput_0,
    id_ctrl_decoder_decoded_andMatrixInput_1,id_ctrl_decoder_decoded_andMatrixInput_2,
    id_ctrl_decoder_decoded_andMatrixInput_3,id_ctrl_decoder_decoded_andMatrixInput_4_6,
    id_ctrl_decoder_decoded_andMatrixInput_5,id_ctrl_decoder_decoded_andMatrixInput_6,
    id_ctrl_decoder_decoded_andMatrixInput_7_17,id_ctrl_decoder_decoded_lo_40}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_T_81 = &_id_ctrl_decoder_decoded_T_80; // @[pla.scala 98:74]
  wire [7:0] id_ctrl_decoder_decoded_lo_41 = {id_ctrl_decoder_decoded_andMatrixInput_8_22,
    id_ctrl_decoder_decoded_andMatrixInput_10,id_ctrl_decoder_decoded_andMatrixInput_11,
    id_ctrl_decoder_decoded_andMatrixInput_12,id_ctrl_decoder_decoded_andMatrixInput_13,
    id_ctrl_decoder_decoded_andMatrixInput_14,id_ctrl_decoder_decoded_andMatrixInput_11_1,
    id_ctrl_decoder_decoded_andMatrixInput_15}; // @[Cat.scala 31:58]
  wire [15:0] _id_ctrl_decoder_decoded_T_82 = {id_ctrl_decoder_decoded_andMatrixInput_0,
    id_ctrl_decoder_decoded_andMatrixInput_1,id_ctrl_decoder_decoded_andMatrixInput_2,
    id_ctrl_decoder_decoded_andMatrixInput_3,id_ctrl_decoder_decoded_andMatrixInput_4_6,
    id_ctrl_decoder_decoded_andMatrixInput_6,id_ctrl_decoder_decoded_andMatrixInput_7_17,
    id_ctrl_decoder_decoded_andMatrixInput_7,id_ctrl_decoder_decoded_lo_41}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_T_83 = &_id_ctrl_decoder_decoded_T_82; // @[pla.scala 98:74]
  wire [15:0] _id_ctrl_decoder_decoded_T_84 = {id_ctrl_decoder_decoded_andMatrixInput_0,
    id_ctrl_decoder_decoded_andMatrixInput_1,id_ctrl_decoder_decoded_andMatrixInput_2,
    id_ctrl_decoder_decoded_andMatrixInput_3,id_ctrl_decoder_decoded_andMatrixInput_4_6,
    id_ctrl_decoder_decoded_andMatrixInput_5_8,id_ctrl_decoder_decoded_andMatrixInput_6,
    id_ctrl_decoder_decoded_andMatrixInput_7_17,id_ctrl_decoder_decoded_lo_40}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_T_85 = &_id_ctrl_decoder_decoded_T_84; // @[pla.scala 98:74]
  wire [14:0] _id_ctrl_decoder_decoded_T_86 = {id_ctrl_decoder_decoded_andMatrixInput_0,
    id_ctrl_decoder_decoded_andMatrixInput_1,id_ctrl_decoder_decoded_andMatrixInput_2,
    id_ctrl_decoder_decoded_andMatrixInput_3,id_ctrl_decoder_decoded_andMatrixInput_4_6,
    id_ctrl_decoder_decoded_andMatrixInput_5_8,id_ctrl_decoder_decoded_andMatrixInput_6,
    id_ctrl_decoder_decoded_andMatrixInput_7_17,id_ctrl_decoder_decoded_lo_37}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_T_87 = &_id_ctrl_decoder_decoded_T_86; // @[pla.scala 98:74]
  wire [7:0] _id_ctrl_decoder_decoded_T_88 = {id_ctrl_decoder_decoded_andMatrixInput_0,
    id_ctrl_decoder_decoded_andMatrixInput_1,id_ctrl_decoder_decoded_andMatrixInput_2,
    id_ctrl_decoder_decoded_andMatrixInput_3,id_ctrl_decoder_decoded_andMatrixInput_5_8,
    id_ctrl_decoder_decoded_andMatrixInput_6_12,id_ctrl_decoder_decoded_andMatrixInput_7_17,
    id_ctrl_decoder_decoded_andMatrixInput_8_22}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_T_89 = &_id_ctrl_decoder_decoded_T_88; // @[pla.scala 98:74]
  wire [8:0] _id_ctrl_decoder_decoded_T_90 = {id_ctrl_decoder_decoded_andMatrixInput_0,
    id_ctrl_decoder_decoded_andMatrixInput_1,id_ctrl_decoder_decoded_andMatrixInput_2,
    id_ctrl_decoder_decoded_andMatrixInput_3,id_ctrl_decoder_decoded_andMatrixInput_4,
    id_ctrl_decoder_decoded_andMatrixInput_5_8,id_ctrl_decoder_decoded_andMatrixInput_6_12,
    id_ctrl_decoder_decoded_andMatrixInput_7_17,id_ctrl_decoder_decoded_andMatrixInput_8_22}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_T_91 = &_id_ctrl_decoder_decoded_T_90; // @[pla.scala 98:74]
  wire [8:0] _id_ctrl_decoder_decoded_T_92 = {id_ctrl_decoder_decoded_andMatrixInput_0,
    id_ctrl_decoder_decoded_andMatrixInput_1,id_ctrl_decoder_decoded_andMatrixInput_2,
    id_ctrl_decoder_decoded_andMatrixInput_3,id_ctrl_decoder_decoded_andMatrixInput_4_6,
    id_ctrl_decoder_decoded_andMatrixInput_5_8,id_ctrl_decoder_decoded_andMatrixInput_6_12,
    id_ctrl_decoder_decoded_andMatrixInput_7_17,id_ctrl_decoder_decoded_andMatrixInput_8_22}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_T_93 = &_id_ctrl_decoder_decoded_T_92; // @[pla.scala 98:74]
  wire [8:0] _id_ctrl_decoder_decoded_T_94 = {id_ctrl_decoder_decoded_andMatrixInput_0,
    id_ctrl_decoder_decoded_andMatrixInput_1,id_ctrl_decoder_decoded_andMatrixInput_2,
    id_ctrl_decoder_decoded_andMatrixInput_3,id_ctrl_decoder_decoded_andMatrixInput_4_6,
    id_ctrl_decoder_decoded_andMatrixInput_5,id_ctrl_decoder_decoded_andMatrixInput_6,
    id_ctrl_decoder_decoded_andMatrixInput_7_24,id_ctrl_decoder_decoded_andMatrixInput_8_22}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_T_95 = &_id_ctrl_decoder_decoded_T_94; // @[pla.scala 98:74]
  wire [14:0] _id_ctrl_decoder_decoded_T_96 = {id_ctrl_decoder_decoded_andMatrixInput_0,
    id_ctrl_decoder_decoded_andMatrixInput_1,id_ctrl_decoder_decoded_andMatrixInput_2,
    id_ctrl_decoder_decoded_andMatrixInput_3,id_ctrl_decoder_decoded_andMatrixInput_4_6,
    id_ctrl_decoder_decoded_andMatrixInput_5_8,id_ctrl_decoder_decoded_andMatrixInput_6,
    id_ctrl_decoder_decoded_andMatrixInput_7_24,id_ctrl_decoder_decoded_lo_37}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_T_97 = &_id_ctrl_decoder_decoded_T_96; // @[pla.scala 98:74]
  wire [7:0] _id_ctrl_decoder_decoded_T_98 = {id_ctrl_decoder_decoded_andMatrixInput_0,
    id_ctrl_decoder_decoded_andMatrixInput_1,id_ctrl_decoder_decoded_andMatrixInput_2,
    id_ctrl_decoder_decoded_andMatrixInput_3,id_ctrl_decoder_decoded_andMatrixInput_5_8,
    id_ctrl_decoder_decoded_andMatrixInput_6_12,id_ctrl_decoder_decoded_andMatrixInput_7_24,
    id_ctrl_decoder_decoded_andMatrixInput_8_22}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_T_99 = &_id_ctrl_decoder_decoded_T_98; // @[pla.scala 98:74]
  wire [8:0] _id_ctrl_decoder_decoded_T_100 = {id_ctrl_decoder_decoded_andMatrixInput_0,
    id_ctrl_decoder_decoded_andMatrixInput_1,id_ctrl_decoder_decoded_andMatrixInput_2,
    id_ctrl_decoder_decoded_andMatrixInput_3,id_ctrl_decoder_decoded_andMatrixInput_4,
    id_ctrl_decoder_decoded_andMatrixInput_5_8,id_ctrl_decoder_decoded_andMatrixInput_6_12,
    id_ctrl_decoder_decoded_andMatrixInput_7_24,id_ctrl_decoder_decoded_andMatrixInput_8_22}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_T_101 = &_id_ctrl_decoder_decoded_T_100; // @[pla.scala 98:74]
  wire [8:0] _id_ctrl_decoder_decoded_T_102 = {id_ctrl_decoder_decoded_andMatrixInput_0,
    id_ctrl_decoder_decoded_andMatrixInput_1,id_ctrl_decoder_decoded_andMatrixInput_2,
    id_ctrl_decoder_decoded_andMatrixInput_3,id_ctrl_decoder_decoded_andMatrixInput_4_6,
    id_ctrl_decoder_decoded_andMatrixInput_5_8,id_ctrl_decoder_decoded_andMatrixInput_6_12,
    id_ctrl_decoder_decoded_andMatrixInput_7_24,id_ctrl_decoder_decoded_andMatrixInput_8_22}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_T_103 = &_id_ctrl_decoder_decoded_T_102; // @[pla.scala 98:74]
  wire [9:0] _id_ctrl_decoder_decoded_T_104 = {id_ctrl_decoder_decoded_andMatrixInput_0,
    id_ctrl_decoder_decoded_andMatrixInput_1,id_ctrl_decoder_decoded_andMatrixInput_2,
    id_ctrl_decoder_decoded_andMatrixInput_3,id_ctrl_decoder_decoded_andMatrixInput_4_6,
    id_ctrl_decoder_decoded_andMatrixInput_5,id_ctrl_decoder_decoded_andMatrixInput_6,
    id_ctrl_decoder_decoded_andMatrixInput_7_17,id_ctrl_decoder_decoded_andMatrixInput_7_24,
    id_ctrl_decoder_decoded_andMatrixInput_8_22}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_T_105 = &_id_ctrl_decoder_decoded_T_104; // @[pla.scala 98:74]
  wire  id_ctrl_decoder_decoded_andMatrixInput_7_50 = id_ctrl_decoder_decoded_plaInput[25]; // @[pla.scala 90:45]
  wire [6:0] id_ctrl_decoder_decoded_lo_53 = {id_ctrl_decoder_decoded_andMatrixInput_7_50,
    id_ctrl_decoder_decoded_andMatrixInput_11,id_ctrl_decoder_decoded_andMatrixInput_12,
    id_ctrl_decoder_decoded_andMatrixInput_13,id_ctrl_decoder_decoded_andMatrixInput_14,
    id_ctrl_decoder_decoded_andMatrixInput_11_1,id_ctrl_decoder_decoded_andMatrixInput_15}; // @[Cat.scala 31:58]
  wire [13:0] _id_ctrl_decoder_decoded_T_106 = {id_ctrl_decoder_decoded_andMatrixInput_0,
    id_ctrl_decoder_decoded_andMatrixInput_1,id_ctrl_decoder_decoded_andMatrixInput_2,
    id_ctrl_decoder_decoded_andMatrixInput_3,id_ctrl_decoder_decoded_andMatrixInput_4_6,
    id_ctrl_decoder_decoded_andMatrixInput_5_8,id_ctrl_decoder_decoded_andMatrixInput_6,id_ctrl_decoder_decoded_lo_53}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_T_107 = &_id_ctrl_decoder_decoded_T_106; // @[pla.scala 98:74]
  wire [14:0] _id_ctrl_decoder_decoded_T_108 = {id_ctrl_decoder_decoded_andMatrixInput_0,
    id_ctrl_decoder_decoded_andMatrixInput_1,id_ctrl_decoder_decoded_andMatrixInput_2,
    id_ctrl_decoder_decoded_andMatrixInput_3,id_ctrl_decoder_decoded_andMatrixInput_4_6,
    id_ctrl_decoder_decoded_andMatrixInput_5_8,id_ctrl_decoder_decoded_andMatrixInput_6,
    id_ctrl_decoder_decoded_andMatrixInput_7_17,id_ctrl_decoder_decoded_lo_53}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_T_109 = &_id_ctrl_decoder_decoded_T_108; // @[pla.scala 98:74]
  wire [14:0] _id_ctrl_decoder_decoded_T_110 = {id_ctrl_decoder_decoded_andMatrixInput_0,
    id_ctrl_decoder_decoded_andMatrixInput_1,id_ctrl_decoder_decoded_andMatrixInput_2,
    id_ctrl_decoder_decoded_andMatrixInput_3,id_ctrl_decoder_decoded_andMatrixInput_4_6,
    id_ctrl_decoder_decoded_andMatrixInput_5_8,id_ctrl_decoder_decoded_andMatrixInput_6,
    id_ctrl_decoder_decoded_andMatrixInput_7_24,id_ctrl_decoder_decoded_lo_53}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_T_111 = &_id_ctrl_decoder_decoded_T_110; // @[pla.scala 98:74]
  wire  id_ctrl_decoder_decoded_andMatrixInput_10_20 = id_ctrl_decoder_decoded_plaInput[27]; // @[pla.scala 90:45]
  wire [6:0] id_ctrl_decoder_decoded_lo_56 = {id_ctrl_decoder_decoded_andMatrixInput_6_1,
    id_ctrl_decoder_decoded_andMatrixInput_7_24,id_ctrl_decoder_decoded_andMatrixInput_7_2,
    id_ctrl_decoder_decoded_andMatrixInput_10_20,id_ctrl_decoder_decoded_andMatrixInput_14,
    id_ctrl_decoder_decoded_andMatrixInput_11_1,id_ctrl_decoder_decoded_andMatrixInput_15}; // @[Cat.scala 31:58]
  wire [13:0] _id_ctrl_decoder_decoded_T_112 = {id_ctrl_decoder_decoded_andMatrixInput_0,
    id_ctrl_decoder_decoded_andMatrixInput_1,id_ctrl_decoder_decoded_andMatrixInput_2_5,
    id_ctrl_decoder_decoded_andMatrixInput_3_5,id_ctrl_decoder_decoded_andMatrixInput_4,
    id_ctrl_decoder_decoded_andMatrixInput_5_8,id_ctrl_decoder_decoded_andMatrixInput_6,id_ctrl_decoder_decoded_lo_56}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_T_113 = &_id_ctrl_decoder_decoded_T_112; // @[pla.scala 98:74]
  wire  id_ctrl_decoder_decoded_andMatrixInput_7_54 = id_ctrl_decoder_decoded_invInputs[20]; // @[pla.scala 91:29]
  wire  id_ctrl_decoder_decoded_andMatrixInput_13_19 = id_ctrl_decoder_decoded_plaInput[28]; // @[pla.scala 90:45]
  wire [7:0] id_ctrl_decoder_decoded_lo_57 = {id_ctrl_decoder_decoded_andMatrixInput_18,
    id_ctrl_decoder_decoded_andMatrixInput_19,id_ctrl_decoder_decoded_andMatrixInput_20,
    id_ctrl_decoder_decoded_andMatrixInput_12,id_ctrl_decoder_decoded_andMatrixInput_13_19,
    id_ctrl_decoder_decoded_andMatrixInput_14,id_ctrl_decoder_decoded_andMatrixInput_11_1,
    id_ctrl_decoder_decoded_andMatrixInput_15}; // @[Cat.scala 31:58]
  wire [16:0] _id_ctrl_decoder_decoded_T_114 = {id_ctrl_decoder_decoded_andMatrixInput_0,
    id_ctrl_decoder_decoded_andMatrixInput_1,id_ctrl_decoder_decoded_andMatrixInput_2_5,
    id_ctrl_decoder_decoded_andMatrixInput_3_5,id_ctrl_decoder_decoded_andMatrixInput_4,
    id_ctrl_decoder_decoded_andMatrixInput_5_8,id_ctrl_decoder_decoded_andMatrixInput_6,
    id_ctrl_decoder_decoded_andMatrixInput_7_54,id_ctrl_decoder_decoded_andMatrixInput_17,id_ctrl_decoder_decoded_lo_57}
    ; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_T_115 = &_id_ctrl_decoder_decoded_T_114; // @[pla.scala 98:74]
  wire [9:0] id_ctrl_decoder_decoded_lo_58 = {id_ctrl_decoder_decoded_andMatrixInput_7_54,
    id_ctrl_decoder_decoded_andMatrixInput_17,id_ctrl_decoder_decoded_andMatrixInput_18,
    id_ctrl_decoder_decoded_andMatrixInput_19,id_ctrl_decoder_decoded_andMatrixInput_20,
    id_ctrl_decoder_decoded_andMatrixInput_12,id_ctrl_decoder_decoded_andMatrixInput_13_19,
    id_ctrl_decoder_decoded_andMatrixInput_14,id_ctrl_decoder_decoded_andMatrixInput_11_1,
    id_ctrl_decoder_decoded_andMatrixInput_15}; // @[Cat.scala 31:58]
  wire [9:0] id_ctrl_decoder_decoded_hi_58 = {id_ctrl_decoder_decoded_andMatrixInput_0,
    id_ctrl_decoder_decoded_andMatrixInput_1,id_ctrl_decoder_decoded_andMatrixInput_2_5,
    id_ctrl_decoder_decoded_andMatrixInput_3_5,id_ctrl_decoder_decoded_andMatrixInput_4,
    id_ctrl_decoder_decoded_andMatrixInput_5_8,id_ctrl_decoder_decoded_andMatrixInput_6,
    id_ctrl_decoder_decoded_andMatrixInput_6_1,id_ctrl_decoder_decoded_andMatrixInput_7_24,
    id_ctrl_decoder_decoded_andMatrixInput_7_2}; // @[Cat.scala 31:58]
  wire [19:0] _id_ctrl_decoder_decoded_T_116 = {id_ctrl_decoder_decoded_hi_58,id_ctrl_decoder_decoded_lo_58}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_T_117 = &_id_ctrl_decoder_decoded_T_116; // @[pla.scala 98:74]
  wire  id_ctrl_decoder_decoded_andMatrixInput_17_3 = id_ctrl_decoder_decoded_plaInput[20]; // @[pla.scala 90:45]
  wire  id_ctrl_decoder_decoded_andMatrixInput_19_3 = id_ctrl_decoder_decoded_plaInput[22]; // @[pla.scala 90:45]
  wire [6:0] id_ctrl_decoder_decoded_lo_lo_56 = {id_ctrl_decoder_decoded_andMatrixInput_20,
    id_ctrl_decoder_decoded_andMatrixInput_10,id_ctrl_decoder_decoded_andMatrixInput_11,
    id_ctrl_decoder_decoded_andMatrixInput_12,id_ctrl_decoder_decoded_andMatrixInput_13_19,
    id_ctrl_decoder_decoded_andMatrixInput_11_1,id_ctrl_decoder_decoded_andMatrixInput_15}; // @[Cat.scala 31:58]
  wire [13:0] id_ctrl_decoder_decoded_lo_59 = {id_ctrl_decoder_decoded_andMatrixInput_14_1,
    id_ctrl_decoder_decoded_andMatrixInput_15_1,id_ctrl_decoder_decoded_andMatrixInput_16,
    id_ctrl_decoder_decoded_andMatrixInput_17_3,id_ctrl_decoder_decoded_andMatrixInput_17,
    id_ctrl_decoder_decoded_andMatrixInput_19_3,id_ctrl_decoder_decoded_andMatrixInput_19,
    id_ctrl_decoder_decoded_lo_lo_56}; // @[Cat.scala 31:58]
  wire [27:0] _id_ctrl_decoder_decoded_T_118 = {id_ctrl_decoder_decoded_andMatrixInput_0,
    id_ctrl_decoder_decoded_andMatrixInput_4_6,id_ctrl_decoder_decoded_andMatrixInput_5_8,
    id_ctrl_decoder_decoded_andMatrixInput_6_12,id_ctrl_decoder_decoded_andMatrixInput_4_18,
    id_ctrl_decoder_decoded_andMatrixInput_5_18,id_ctrl_decoder_decoded_andMatrixInput_6_17,
    id_ctrl_decoder_decoded_hi_lo_17,id_ctrl_decoder_decoded_lo_59}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_T_119 = &_id_ctrl_decoder_decoded_T_118; // @[pla.scala 98:74]
  wire [14:0] id_ctrl_decoder_decoded_lo_60 = {id_ctrl_decoder_decoded_andMatrixInput_13_1,
    id_ctrl_decoder_decoded_andMatrixInput_14_1,id_ctrl_decoder_decoded_andMatrixInput_15_1,
    id_ctrl_decoder_decoded_andMatrixInput_16,id_ctrl_decoder_decoded_andMatrixInput_17_3,
    id_ctrl_decoder_decoded_andMatrixInput_17,id_ctrl_decoder_decoded_andMatrixInput_19_3,
    id_ctrl_decoder_decoded_andMatrixInput_19,id_ctrl_decoder_decoded_lo_lo_56}; // @[Cat.scala 31:58]
  wire [30:0] _id_ctrl_decoder_decoded_T_120 = {id_ctrl_decoder_decoded_andMatrixInput_0,
    id_ctrl_decoder_decoded_andMatrixInput_1,id_ctrl_decoder_decoded_andMatrixInput_2,
    id_ctrl_decoder_decoded_andMatrixInput_3,id_ctrl_decoder_decoded_andMatrixInput_4_6,
    id_ctrl_decoder_decoded_andMatrixInput_5_8,id_ctrl_decoder_decoded_andMatrixInput_6_12,
    id_ctrl_decoder_decoded_andMatrixInput_4_18,id_ctrl_decoder_decoded_hi_lo_18,id_ctrl_decoder_decoded_lo_60}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_T_121 = &_id_ctrl_decoder_decoded_T_120; // @[pla.scala 98:74]
  wire [6:0] id_ctrl_decoder_decoded_lo_61 = {id_ctrl_decoder_decoded_andMatrixInput_7_24,
    id_ctrl_decoder_decoded_andMatrixInput_7_2,id_ctrl_decoder_decoded_andMatrixInput_10_20,
    id_ctrl_decoder_decoded_andMatrixInput_13_19,id_ctrl_decoder_decoded_andMatrixInput_14,
    id_ctrl_decoder_decoded_andMatrixInput_11_1,id_ctrl_decoder_decoded_andMatrixInput_15}; // @[Cat.scala 31:58]
  wire [14:0] _id_ctrl_decoder_decoded_T_122 = {id_ctrl_decoder_decoded_andMatrixInput_0,
    id_ctrl_decoder_decoded_andMatrixInput_1,id_ctrl_decoder_decoded_andMatrixInput_2_5,
    id_ctrl_decoder_decoded_andMatrixInput_3_5,id_ctrl_decoder_decoded_andMatrixInput_4,
    id_ctrl_decoder_decoded_andMatrixInput_5_8,id_ctrl_decoder_decoded_andMatrixInput_6,
    id_ctrl_decoder_decoded_andMatrixInput_6_1,id_ctrl_decoder_decoded_lo_61}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_T_123 = &_id_ctrl_decoder_decoded_T_122; // @[pla.scala 98:74]
  wire  id_ctrl_decoder_decoded_andMatrixInput_12_25 = id_ctrl_decoder_decoded_plaInput[29]; // @[pla.scala 90:45]
  wire [5:0] id_ctrl_decoder_decoded_lo_62 = {id_ctrl_decoder_decoded_andMatrixInput_6_1,
    id_ctrl_decoder_decoded_andMatrixInput_7_24,id_ctrl_decoder_decoded_andMatrixInput_7_2,
    id_ctrl_decoder_decoded_andMatrixInput_12,id_ctrl_decoder_decoded_andMatrixInput_13,
    id_ctrl_decoder_decoded_andMatrixInput_12_25}; // @[Cat.scala 31:58]
  wire [12:0] _id_ctrl_decoder_decoded_T_124 = {id_ctrl_decoder_decoded_andMatrixInput_0,
    id_ctrl_decoder_decoded_andMatrixInput_1,id_ctrl_decoder_decoded_andMatrixInput_2_5,
    id_ctrl_decoder_decoded_andMatrixInput_3_5,id_ctrl_decoder_decoded_andMatrixInput_4,
    id_ctrl_decoder_decoded_andMatrixInput_5_8,id_ctrl_decoder_decoded_andMatrixInput_6,id_ctrl_decoder_decoded_lo_62}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_T_125 = &_id_ctrl_decoder_decoded_T_124; // @[pla.scala 98:74]
  wire  id_ctrl_decoder_decoded_andMatrixInput_17_5 = id_ctrl_decoder_decoded_plaInput[21]; // @[pla.scala 90:45]
  wire [6:0] id_ctrl_decoder_decoded_lo_lo_60 = {id_ctrl_decoder_decoded_andMatrixInput_10,
    id_ctrl_decoder_decoded_andMatrixInput_11,id_ctrl_decoder_decoded_andMatrixInput_12,
    id_ctrl_decoder_decoded_andMatrixInput_13_19,id_ctrl_decoder_decoded_andMatrixInput_12_25,
    id_ctrl_decoder_decoded_andMatrixInput_11_1,id_ctrl_decoder_decoded_andMatrixInput_15}; // @[Cat.scala 31:58]
  wire [13:0] id_ctrl_decoder_decoded_lo_63 = {id_ctrl_decoder_decoded_andMatrixInput_15_1,
    id_ctrl_decoder_decoded_andMatrixInput_16,id_ctrl_decoder_decoded_andMatrixInput_7_54,
    id_ctrl_decoder_decoded_andMatrixInput_17_5,id_ctrl_decoder_decoded_andMatrixInput_18,
    id_ctrl_decoder_decoded_andMatrixInput_19,id_ctrl_decoder_decoded_andMatrixInput_20,id_ctrl_decoder_decoded_lo_lo_60
    }; // @[Cat.scala 31:58]
  wire [6:0] id_ctrl_decoder_decoded_hi_lo_62 = {id_ctrl_decoder_decoded_andMatrixInput_8_8,
    id_ctrl_decoder_decoded_andMatrixInput_6_1,id_ctrl_decoder_decoded_andMatrixInput_7,
    id_ctrl_decoder_decoded_andMatrixInput_7_2,id_ctrl_decoder_decoded_andMatrixInput_12_2,
    id_ctrl_decoder_decoded_andMatrixInput_13_1,id_ctrl_decoder_decoded_andMatrixInput_14_1}; // @[Cat.scala 31:58]
  wire [27:0] _id_ctrl_decoder_decoded_T_126 = {id_ctrl_decoder_decoded_andMatrixInput_4_6,
    id_ctrl_decoder_decoded_andMatrixInput_5_8,id_ctrl_decoder_decoded_andMatrixInput_6_12,
    id_ctrl_decoder_decoded_andMatrixInput_4_18,id_ctrl_decoder_decoded_andMatrixInput_5_18,
    id_ctrl_decoder_decoded_andMatrixInput_6_17,id_ctrl_decoder_decoded_andMatrixInput_7_15,
    id_ctrl_decoder_decoded_hi_lo_62,id_ctrl_decoder_decoded_lo_63}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_T_127 = &_id_ctrl_decoder_decoded_T_126; // @[pla.scala 98:74]
  wire [7:0] id_ctrl_decoder_decoded_lo_lo_61 = {id_ctrl_decoder_decoded_andMatrixInput_20,
    id_ctrl_decoder_decoded_andMatrixInput_10,id_ctrl_decoder_decoded_andMatrixInput_11,
    id_ctrl_decoder_decoded_andMatrixInput_12,id_ctrl_decoder_decoded_andMatrixInput_13_19,
    id_ctrl_decoder_decoded_andMatrixInput_12_25,id_ctrl_decoder_decoded_andMatrixInput_11_1,
    id_ctrl_decoder_decoded_andMatrixInput_15}; // @[Cat.scala 31:58]
  wire [15:0] id_ctrl_decoder_decoded_lo_64 = {id_ctrl_decoder_decoded_andMatrixInput_13_1,
    id_ctrl_decoder_decoded_andMatrixInput_14_1,id_ctrl_decoder_decoded_andMatrixInput_15_1,
    id_ctrl_decoder_decoded_andMatrixInput_16,id_ctrl_decoder_decoded_andMatrixInput_7_54,
    id_ctrl_decoder_decoded_andMatrixInput_17_5,id_ctrl_decoder_decoded_andMatrixInput_18,
    id_ctrl_decoder_decoded_andMatrixInput_19,id_ctrl_decoder_decoded_lo_lo_61}; // @[Cat.scala 31:58]
  wire [31:0] _id_ctrl_decoder_decoded_T_128 = {id_ctrl_decoder_decoded_andMatrixInput_0,
    id_ctrl_decoder_decoded_andMatrixInput_1,id_ctrl_decoder_decoded_andMatrixInput_2,
    id_ctrl_decoder_decoded_andMatrixInput_3,id_ctrl_decoder_decoded_andMatrixInput_4_6,
    id_ctrl_decoder_decoded_andMatrixInput_5_8,id_ctrl_decoder_decoded_andMatrixInput_6_12,
    id_ctrl_decoder_decoded_andMatrixInput_4_18,id_ctrl_decoder_decoded_hi_lo_18,id_ctrl_decoder_decoded_lo_64}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_T_129 = &_id_ctrl_decoder_decoded_T_128; // @[pla.scala 98:74]
  wire  id_ctrl_decoder_decoded_andMatrixInput_15_14 = id_ctrl_decoder_decoded_plaInput[30]; // @[pla.scala 90:45]
  wire [7:0] id_ctrl_decoder_decoded_lo_65 = {id_ctrl_decoder_decoded_andMatrixInput_7_2,
    id_ctrl_decoder_decoded_andMatrixInput_10,id_ctrl_decoder_decoded_andMatrixInput_11,
    id_ctrl_decoder_decoded_andMatrixInput_12,id_ctrl_decoder_decoded_andMatrixInput_13,
    id_ctrl_decoder_decoded_andMatrixInput_14,id_ctrl_decoder_decoded_andMatrixInput_15_14,
    id_ctrl_decoder_decoded_andMatrixInput_15}; // @[Cat.scala 31:58]
  wire [16:0] _id_ctrl_decoder_decoded_T_130 = {id_ctrl_decoder_decoded_andMatrixInput_0,
    id_ctrl_decoder_decoded_andMatrixInput_1,id_ctrl_decoder_decoded_andMatrixInput_2,
    id_ctrl_decoder_decoded_andMatrixInput_3,id_ctrl_decoder_decoded_andMatrixInput_4_6,
    id_ctrl_decoder_decoded_andMatrixInput_5_8,id_ctrl_decoder_decoded_andMatrixInput_6,
    id_ctrl_decoder_decoded_andMatrixInput_6_1,id_ctrl_decoder_decoded_andMatrixInput_7,id_ctrl_decoder_decoded_lo_65}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_T_131 = &_id_ctrl_decoder_decoded_T_130; // @[pla.scala 98:74]
  wire [5:0] id_ctrl_decoder_decoded_lo_66 = {id_ctrl_decoder_decoded_andMatrixInput_6_1,
    id_ctrl_decoder_decoded_andMatrixInput_7_24,id_ctrl_decoder_decoded_andMatrixInput_7_2,
    id_ctrl_decoder_decoded_andMatrixInput_12,id_ctrl_decoder_decoded_andMatrixInput_13,
    id_ctrl_decoder_decoded_andMatrixInput_15_14}; // @[Cat.scala 31:58]
  wire [12:0] _id_ctrl_decoder_decoded_T_132 = {id_ctrl_decoder_decoded_andMatrixInput_0,
    id_ctrl_decoder_decoded_andMatrixInput_1,id_ctrl_decoder_decoded_andMatrixInput_2_5,
    id_ctrl_decoder_decoded_andMatrixInput_3_5,id_ctrl_decoder_decoded_andMatrixInput_4,
    id_ctrl_decoder_decoded_andMatrixInput_5_8,id_ctrl_decoder_decoded_andMatrixInput_6,id_ctrl_decoder_decoded_lo_66}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_T_133 = &_id_ctrl_decoder_decoded_T_132; // @[pla.scala 98:74]
  wire [7:0] id_ctrl_decoder_decoded_lo_67 = {id_ctrl_decoder_decoded_andMatrixInput_8_22,
    id_ctrl_decoder_decoded_andMatrixInput_10,id_ctrl_decoder_decoded_andMatrixInput_11,
    id_ctrl_decoder_decoded_andMatrixInput_12,id_ctrl_decoder_decoded_andMatrixInput_13,
    id_ctrl_decoder_decoded_andMatrixInput_14,id_ctrl_decoder_decoded_andMatrixInput_15_14,
    id_ctrl_decoder_decoded_andMatrixInput_15}; // @[Cat.scala 31:58]
  wire [15:0] _id_ctrl_decoder_decoded_T_134 = {id_ctrl_decoder_decoded_andMatrixInput_0,
    id_ctrl_decoder_decoded_andMatrixInput_1,id_ctrl_decoder_decoded_andMatrixInput_2,
    id_ctrl_decoder_decoded_andMatrixInput_3,id_ctrl_decoder_decoded_andMatrixInput_4_6,
    id_ctrl_decoder_decoded_andMatrixInput_6,id_ctrl_decoder_decoded_andMatrixInput_7_17,
    id_ctrl_decoder_decoded_andMatrixInput_7,id_ctrl_decoder_decoded_lo_67}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_T_135 = &_id_ctrl_decoder_decoded_T_134; // @[pla.scala 98:74]
  wire  id_ctrl_decoder_decoded_andMatrixInput_20_6 = id_ctrl_decoder_decoded_plaInput[24]; // @[pla.scala 90:45]
  wire [6:0] id_ctrl_decoder_decoded_lo_lo_65 = {id_ctrl_decoder_decoded_andMatrixInput_7_50,
    id_ctrl_decoder_decoded_andMatrixInput_11,id_ctrl_decoder_decoded_andMatrixInput_10_20,
    id_ctrl_decoder_decoded_andMatrixInput_13_19,id_ctrl_decoder_decoded_andMatrixInput_12_25,
    id_ctrl_decoder_decoded_andMatrixInput_15_14,id_ctrl_decoder_decoded_andMatrixInput_15}; // @[Cat.scala 31:58]
  wire [13:0] id_ctrl_decoder_decoded_lo_68 = {id_ctrl_decoder_decoded_andMatrixInput_15_1,
    id_ctrl_decoder_decoded_andMatrixInput_16,id_ctrl_decoder_decoded_andMatrixInput_7_54,
    id_ctrl_decoder_decoded_andMatrixInput_17_5,id_ctrl_decoder_decoded_andMatrixInput_18,
    id_ctrl_decoder_decoded_andMatrixInput_19,id_ctrl_decoder_decoded_andMatrixInput_20_6,
    id_ctrl_decoder_decoded_lo_lo_65}; // @[Cat.scala 31:58]
  wire [27:0] _id_ctrl_decoder_decoded_T_136 = {id_ctrl_decoder_decoded_andMatrixInput_4_6,
    id_ctrl_decoder_decoded_andMatrixInput_5_8,id_ctrl_decoder_decoded_andMatrixInput_6_12,
    id_ctrl_decoder_decoded_andMatrixInput_4_18,id_ctrl_decoder_decoded_andMatrixInput_5_18,
    id_ctrl_decoder_decoded_andMatrixInput_6_17,id_ctrl_decoder_decoded_andMatrixInput_7_15,
    id_ctrl_decoder_decoded_hi_lo_62,id_ctrl_decoder_decoded_lo_68}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_T_137 = &_id_ctrl_decoder_decoded_T_136; // @[pla.scala 98:74]
  wire [7:0] id_ctrl_decoder_decoded_lo_lo_66 = {id_ctrl_decoder_decoded_andMatrixInput_20_6,
    id_ctrl_decoder_decoded_andMatrixInput_7_50,id_ctrl_decoder_decoded_andMatrixInput_11,
    id_ctrl_decoder_decoded_andMatrixInput_10_20,id_ctrl_decoder_decoded_andMatrixInput_13_19,
    id_ctrl_decoder_decoded_andMatrixInput_12_25,id_ctrl_decoder_decoded_andMatrixInput_15_14,
    id_ctrl_decoder_decoded_andMatrixInput_15}; // @[Cat.scala 31:58]
  wire [15:0] id_ctrl_decoder_decoded_lo_69 = {id_ctrl_decoder_decoded_andMatrixInput_13_1,
    id_ctrl_decoder_decoded_andMatrixInput_14_1,id_ctrl_decoder_decoded_andMatrixInput_15_1,
    id_ctrl_decoder_decoded_andMatrixInput_16,id_ctrl_decoder_decoded_andMatrixInput_7_54,
    id_ctrl_decoder_decoded_andMatrixInput_17_5,id_ctrl_decoder_decoded_andMatrixInput_18,
    id_ctrl_decoder_decoded_andMatrixInput_19,id_ctrl_decoder_decoded_lo_lo_66}; // @[Cat.scala 31:58]
  wire [31:0] _id_ctrl_decoder_decoded_T_138 = {id_ctrl_decoder_decoded_andMatrixInput_0,
    id_ctrl_decoder_decoded_andMatrixInput_1,id_ctrl_decoder_decoded_andMatrixInput_2,
    id_ctrl_decoder_decoded_andMatrixInput_3,id_ctrl_decoder_decoded_andMatrixInput_4_6,
    id_ctrl_decoder_decoded_andMatrixInput_5_8,id_ctrl_decoder_decoded_andMatrixInput_6_12,
    id_ctrl_decoder_decoded_andMatrixInput_4_18,id_ctrl_decoder_decoded_hi_lo_18,id_ctrl_decoder_decoded_lo_69}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_T_139 = &_id_ctrl_decoder_decoded_T_138; // @[pla.scala 98:74]
  wire  id_ctrl_decoder_decoded_andMatrixInput_12_33 = id_ctrl_decoder_decoded_plaInput[31]; // @[pla.scala 90:45]
  wire [5:0] id_ctrl_decoder_decoded_lo_70 = {id_ctrl_decoder_decoded_andMatrixInput_6_1,
    id_ctrl_decoder_decoded_andMatrixInput_7_24,id_ctrl_decoder_decoded_andMatrixInput_7_2,
    id_ctrl_decoder_decoded_andMatrixInput_12,id_ctrl_decoder_decoded_andMatrixInput_13,
    id_ctrl_decoder_decoded_andMatrixInput_12_33}; // @[Cat.scala 31:58]
  wire [12:0] _id_ctrl_decoder_decoded_T_140 = {id_ctrl_decoder_decoded_andMatrixInput_0,
    id_ctrl_decoder_decoded_andMatrixInput_1,id_ctrl_decoder_decoded_andMatrixInput_2_5,
    id_ctrl_decoder_decoded_andMatrixInput_3_5,id_ctrl_decoder_decoded_andMatrixInput_4,
    id_ctrl_decoder_decoded_andMatrixInput_5_8,id_ctrl_decoder_decoded_andMatrixInput_6,id_ctrl_decoder_decoded_lo_70}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_T_141 = &_id_ctrl_decoder_decoded_T_140; // @[pla.scala 98:74]
  wire [2:0] _id_ctrl_decoder_decoded_orMatrixOutputs_T = {_id_ctrl_decoder_decoded_T_59,_id_ctrl_decoder_decoded_T_113,
    _id_ctrl_decoder_decoded_T_115}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_orMatrixOutputs_T_1 = |_id_ctrl_decoder_decoded_orMatrixOutputs_T; // @[pla.scala 114:39]
  wire  _id_ctrl_decoder_decoded_orMatrixOutputs_T_2 = |_id_ctrl_decoder_decoded_T_11; // @[pla.scala 114:39]
  wire  _id_ctrl_decoder_decoded_orMatrixOutputs_T_3 = |_id_ctrl_decoder_decoded_T_41; // @[pla.scala 114:39]
  wire  _id_ctrl_decoder_decoded_orMatrixOutputs_T_4 = |_id_ctrl_decoder_decoded_T_53; // @[pla.scala 114:39]
  wire  _id_ctrl_decoder_decoded_orMatrixOutputs_T_5 = |_id_ctrl_decoder_decoded_T_65; // @[pla.scala 114:39]
  wire [5:0] _id_ctrl_decoder_decoded_orMatrixOutputs_T_6 = {_id_ctrl_decoder_decoded_T_37,_id_ctrl_decoder_decoded_T_53
    ,_id_ctrl_decoder_decoded_T_65,_id_ctrl_decoder_decoded_T_119,_id_ctrl_decoder_decoded_T_127,
    _id_ctrl_decoder_decoded_T_137}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_orMatrixOutputs_T_7 = |_id_ctrl_decoder_decoded_orMatrixOutputs_T_6; // @[pla.scala 114:39]
  wire [7:0] id_ctrl_decoder_decoded_orMatrixOutputs_lo_1 = {_id_ctrl_decoder_decoded_T_43,_id_ctrl_decoder_decoded_T_53
    ,_id_ctrl_decoder_decoded_T_55,_id_ctrl_decoder_decoded_T_59,_id_ctrl_decoder_decoded_T_65,
    _id_ctrl_decoder_decoded_T_79,_id_ctrl_decoder_decoded_T_113,_id_ctrl_decoder_decoded_T_115}; // @[Cat.scala 31:58]
  wire [15:0] _id_ctrl_decoder_decoded_orMatrixOutputs_T_8 = {_id_ctrl_decoder_decoded_T_1,_id_ctrl_decoder_decoded_T_3,
    _id_ctrl_decoder_decoded_T_7,_id_ctrl_decoder_decoded_T_13,_id_ctrl_decoder_decoded_T_23,
    _id_ctrl_decoder_decoded_T_25,_id_ctrl_decoder_decoded_T_33,_id_ctrl_decoder_decoded_T_35,
    id_ctrl_decoder_decoded_orMatrixOutputs_lo_1}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_orMatrixOutputs_T_9 = |_id_ctrl_decoder_decoded_orMatrixOutputs_T_8; // @[pla.scala 114:39]
  wire  _id_ctrl_decoder_decoded_orMatrixOutputs_T_10 = |_id_ctrl_decoder_decoded_T_107; // @[pla.scala 114:39]
  wire [3:0] _id_ctrl_decoder_decoded_orMatrixOutputs_T_11 = {_id_ctrl_decoder_decoded_T_17,
    _id_ctrl_decoder_decoded_T_21,_id_ctrl_decoder_decoded_T_123,_id_ctrl_decoder_decoded_T_125}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_orMatrixOutputs_T_12 = |_id_ctrl_decoder_decoded_orMatrixOutputs_T_11; // @[pla.scala 114:39]
  wire [2:0] _id_ctrl_decoder_decoded_orMatrixOutputs_T_13 = {_id_ctrl_decoder_decoded_T_115,
    _id_ctrl_decoder_decoded_T_123,_id_ctrl_decoder_decoded_T_133}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_orMatrixOutputs_T_14 = |_id_ctrl_decoder_decoded_orMatrixOutputs_T_13; // @[pla.scala 114:39]
  wire [2:0] _id_ctrl_decoder_decoded_orMatrixOutputs_T_15 = {_id_ctrl_decoder_decoded_T_113,
    _id_ctrl_decoder_decoded_T_115,_id_ctrl_decoder_decoded_T_141}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_orMatrixOutputs_T_16 = |_id_ctrl_decoder_decoded_orMatrixOutputs_T_15; // @[pla.scala 114:39]
  wire  _id_ctrl_decoder_decoded_orMatrixOutputs_T_17 = |_id_ctrl_decoder_decoded_T_59; // @[pla.scala 114:39]
  wire [5:0] _id_ctrl_decoder_decoded_orMatrixOutputs_T_18 = {_id_ctrl_decoder_decoded_T_1,_id_ctrl_decoder_decoded_T_5,
    _id_ctrl_decoder_decoded_T_9,_id_ctrl_decoder_decoded_T_59,_id_ctrl_decoder_decoded_T_113,
    _id_ctrl_decoder_decoded_T_117}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_orMatrixOutputs_T_19 = |_id_ctrl_decoder_decoded_orMatrixOutputs_T_18; // @[pla.scala 114:39]
  wire [6:0] _id_ctrl_decoder_decoded_orMatrixOutputs_T_20 = {_id_ctrl_decoder_decoded_T_43,
    _id_ctrl_decoder_decoded_T_49,_id_ctrl_decoder_decoded_T_79,_id_ctrl_decoder_decoded_T_87,
    _id_ctrl_decoder_decoded_T_91,_id_ctrl_decoder_decoded_T_105,_id_ctrl_decoder_decoded_T_109}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_orMatrixOutputs_T_21 = |_id_ctrl_decoder_decoded_orMatrixOutputs_T_20; // @[pla.scala 114:39]
  wire [8:0] _id_ctrl_decoder_decoded_orMatrixOutputs_T_22 = {_id_ctrl_decoder_decoded_T_29,
    _id_ctrl_decoder_decoded_T_69,_id_ctrl_decoder_decoded_T_71,_id_ctrl_decoder_decoded_T_95,
    _id_ctrl_decoder_decoded_T_97,_id_ctrl_decoder_decoded_T_101,_id_ctrl_decoder_decoded_T_111,
    _id_ctrl_decoder_decoded_T_131,_id_ctrl_decoder_decoded_T_135}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_orMatrixOutputs_T_23 = |_id_ctrl_decoder_decoded_orMatrixOutputs_T_22; // @[pla.scala 114:39]
  wire [5:0] _id_ctrl_decoder_decoded_orMatrixOutputs_T_24 = {_id_ctrl_decoder_decoded_T_55,
    _id_ctrl_decoder_decoded_T_61,_id_ctrl_decoder_decoded_T_73,_id_ctrl_decoder_decoded_T_75,
    _id_ctrl_decoder_decoded_T_77,_id_ctrl_decoder_decoded_T_83}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_orMatrixOutputs_T_25 = |_id_ctrl_decoder_decoded_orMatrixOutputs_T_24; // @[pla.scala 114:39]
  wire [4:0] _id_ctrl_decoder_decoded_orMatrixOutputs_T_26 = {_id_ctrl_decoder_decoded_T_57,
    _id_ctrl_decoder_decoded_T_63,_id_ctrl_decoder_decoded_T_77,_id_ctrl_decoder_decoded_T_131,
    _id_ctrl_decoder_decoded_T_135}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_orMatrixOutputs_T_27 = |_id_ctrl_decoder_decoded_orMatrixOutputs_T_26; // @[pla.scala 114:39]
  wire [16:0] _id_ctrl_decoder_decoded_orMatrixOutputs_T_28 = {_id_ctrl_decoder_decoded_T_1,_id_ctrl_decoder_decoded_T_3
    ,_id_ctrl_decoder_decoded_T_5,_id_ctrl_decoder_decoded_T_9,_id_ctrl_decoder_decoded_T_13,
    _id_ctrl_decoder_decoded_T_23,_id_ctrl_decoder_decoded_T_25,_id_ctrl_decoder_decoded_T_33,
    _id_ctrl_decoder_decoded_T_35,id_ctrl_decoder_decoded_orMatrixOutputs_lo_1}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_orMatrixOutputs_T_29 = |_id_ctrl_decoder_decoded_orMatrixOutputs_T_28; // @[pla.scala 114:39]
  wire [3:0] _id_ctrl_decoder_decoded_orMatrixOutputs_T_30 = {_id_ctrl_decoder_decoded_T_27,
    _id_ctrl_decoder_decoded_T_35,_id_ctrl_decoder_decoded_T_89,_id_ctrl_decoder_decoded_T_99}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_orMatrixOutputs_T_31 = |_id_ctrl_decoder_decoded_orMatrixOutputs_T_30; // @[pla.scala 114:39]
  wire [1:0] _id_ctrl_decoder_decoded_orMatrixOutputs_T_32 = {_id_ctrl_decoder_decoded_T_13,
    _id_ctrl_decoder_decoded_T_35}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_orMatrixOutputs_T_33 = |_id_ctrl_decoder_decoded_orMatrixOutputs_T_32; // @[pla.scala 114:39]
  wire [8:0] _id_ctrl_decoder_decoded_orMatrixOutputs_T_34 = {_id_ctrl_decoder_decoded_T_1,_id_ctrl_decoder_decoded_T_3,
    _id_ctrl_decoder_decoded_T_7,_id_ctrl_decoder_decoded_T_33,_id_ctrl_decoder_decoded_T_45,
    _id_ctrl_decoder_decoded_T_55,_id_ctrl_decoder_decoded_T_81,_id_ctrl_decoder_decoded_T_93,
    _id_ctrl_decoder_decoded_T_103}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_orMatrixOutputs_T_35 = |_id_ctrl_decoder_decoded_orMatrixOutputs_T_34; // @[pla.scala 114:39]
  wire [7:0] id_ctrl_decoder_decoded_orMatrixOutputs_lo_11 = {_id_ctrl_decoder_decoded_T_51,
    _id_ctrl_decoder_decoded_T_55,_id_ctrl_decoder_decoded_T_59,_id_ctrl_decoder_decoded_T_67,
    _id_ctrl_decoder_decoded_T_77,_id_ctrl_decoder_decoded_T_79,_id_ctrl_decoder_decoded_T_113,
    _id_ctrl_decoder_decoded_T_115}; // @[Cat.scala 31:58]
  wire [15:0] _id_ctrl_decoder_decoded_orMatrixOutputs_T_36 = {_id_ctrl_decoder_decoded_T_1,_id_ctrl_decoder_decoded_T_3
    ,_id_ctrl_decoder_decoded_T_5,_id_ctrl_decoder_decoded_T_9,_id_ctrl_decoder_decoded_T_23,
    _id_ctrl_decoder_decoded_T_25,_id_ctrl_decoder_decoded_T_31,_id_ctrl_decoder_decoded_T_43,
    id_ctrl_decoder_decoded_orMatrixOutputs_lo_11}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_orMatrixOutputs_T_37 = |_id_ctrl_decoder_decoded_orMatrixOutputs_T_36; // @[pla.scala 114:39]
  wire [1:0] _id_ctrl_decoder_decoded_orMatrixOutputs_T_38 = {_id_ctrl_decoder_decoded_T_15,
    _id_ctrl_decoder_decoded_T_35}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_orMatrixOutputs_T_39 = |_id_ctrl_decoder_decoded_orMatrixOutputs_T_38; // @[pla.scala 114:39]
  wire [5:0] id_ctrl_decoder_decoded_orMatrixOutputs_lo_12 = {_id_ctrl_decoder_decoded_T_35,
    _id_ctrl_decoder_decoded_T_45,_id_ctrl_decoder_decoded_T_55,_id_ctrl_decoder_decoded_T_81,
    _id_ctrl_decoder_decoded_T_93,_id_ctrl_decoder_decoded_T_103}; // @[Cat.scala 31:58]
  wire [11:0] _id_ctrl_decoder_decoded_orMatrixOutputs_T_40 = {_id_ctrl_decoder_decoded_T_1,_id_ctrl_decoder_decoded_T_3
    ,_id_ctrl_decoder_decoded_T_5,_id_ctrl_decoder_decoded_T_9,_id_ctrl_decoder_decoded_T_13,
    _id_ctrl_decoder_decoded_T_33,id_ctrl_decoder_decoded_orMatrixOutputs_lo_12}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_orMatrixOutputs_T_41 = |_id_ctrl_decoder_decoded_orMatrixOutputs_T_40; // @[pla.scala 114:39]
  wire [6:0] id_ctrl_decoder_decoded_orMatrixOutputs_lo_13 = {_id_ctrl_decoder_decoded_T_27,
    _id_ctrl_decoder_decoded_T_31,_id_ctrl_decoder_decoded_T_43,_id_ctrl_decoder_decoded_T_55,
    _id_ctrl_decoder_decoded_T_79,_id_ctrl_decoder_decoded_T_89,_id_ctrl_decoder_decoded_T_99}; // @[Cat.scala 31:58]
  wire [13:0] _id_ctrl_decoder_decoded_orMatrixOutputs_T_42 = {_id_ctrl_decoder_decoded_T_1,_id_ctrl_decoder_decoded_T_3
    ,_id_ctrl_decoder_decoded_T_5,_id_ctrl_decoder_decoded_T_9,_id_ctrl_decoder_decoded_T_13,
    _id_ctrl_decoder_decoded_T_23,_id_ctrl_decoder_decoded_T_25,id_ctrl_decoder_decoded_orMatrixOutputs_lo_13}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_orMatrixOutputs_T_43 = |_id_ctrl_decoder_decoded_orMatrixOutputs_T_42; // @[pla.scala 114:39]
  wire [8:0] _id_ctrl_decoder_decoded_orMatrixOutputs_T_46 = {_id_ctrl_decoder_decoded_T_17,
    _id_ctrl_decoder_decoded_T_19,_id_ctrl_decoder_decoded_T_23,_id_ctrl_decoder_decoded_T_25,
    _id_ctrl_decoder_decoded_T_59,_id_ctrl_decoder_decoded_T_77,_id_ctrl_decoder_decoded_T_85,
    _id_ctrl_decoder_decoded_T_113,_id_ctrl_decoder_decoded_T_115}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_orMatrixOutputs_T_47 = |_id_ctrl_decoder_decoded_orMatrixOutputs_T_46; // @[pla.scala 114:39]
  wire  _id_ctrl_decoder_decoded_orMatrixOutputs_T_48 = |_id_ctrl_decoder_decoded_T_33; // @[pla.scala 114:39]
  wire  _id_ctrl_decoder_decoded_orMatrixOutputs_T_49 = |_id_ctrl_decoder_decoded_T_35; // @[pla.scala 114:39]
  wire [1:0] _id_ctrl_decoder_decoded_orMatrixOutputs_T_50 = {_id_ctrl_decoder_decoded_T_27,
    _id_ctrl_decoder_decoded_T_77}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_orMatrixOutputs_T_51 = |_id_ctrl_decoder_decoded_orMatrixOutputs_T_50; // @[pla.scala 114:39]
  wire [4:0] id_ctrl_decoder_decoded_orMatrixOutputs_lo_lo_9 = {_id_ctrl_decoder_decoded_T_113,
    _id_ctrl_decoder_decoded_T_117,_id_ctrl_decoder_decoded_T_121,_id_ctrl_decoder_decoded_T_129,
    _id_ctrl_decoder_decoded_T_139}; // @[Cat.scala 31:58]
  wire [10:0] id_ctrl_decoder_decoded_orMatrixOutputs_lo_16 = {_id_ctrl_decoder_decoded_T_47,
    _id_ctrl_decoder_decoded_T_55,_id_ctrl_decoder_decoded_T_59,_id_ctrl_decoder_decoded_T_65,
    _id_ctrl_decoder_decoded_T_77,_id_ctrl_decoder_decoded_T_79,id_ctrl_decoder_decoded_orMatrixOutputs_lo_lo_9}; // @[Cat.scala 31:58]
  wire [5:0] id_ctrl_decoder_decoded_orMatrixOutputs_hi_lo_10 = {_id_ctrl_decoder_decoded_T_23,
    _id_ctrl_decoder_decoded_T_25,_id_ctrl_decoder_decoded_T_31,_id_ctrl_decoder_decoded_T_35,
    _id_ctrl_decoder_decoded_T_39,_id_ctrl_decoder_decoded_T_43}; // @[Cat.scala 31:58]
  wire [22:0] _id_ctrl_decoder_decoded_orMatrixOutputs_T_52 = {_id_ctrl_decoder_decoded_T_1,_id_ctrl_decoder_decoded_T_3
    ,_id_ctrl_decoder_decoded_T_5,_id_ctrl_decoder_decoded_T_9,_id_ctrl_decoder_decoded_T_11,
    _id_ctrl_decoder_decoded_T_13,id_ctrl_decoder_decoded_orMatrixOutputs_hi_lo_10,
    id_ctrl_decoder_decoded_orMatrixOutputs_lo_16}; // @[Cat.scala 31:58]
  wire  _id_ctrl_decoder_decoded_orMatrixOutputs_T_53 = |_id_ctrl_decoder_decoded_orMatrixOutputs_T_52; // @[pla.scala 114:39]
  wire [9:0] id_ctrl_decoder_decoded_orMatrixOutputs_lo_lo_10 = {1'h0,_id_ctrl_decoder_decoded_orMatrixOutputs_T_10,
    _id_ctrl_decoder_decoded_orMatrixOutputs_T_9,_id_ctrl_decoder_decoded_orMatrixOutputs_T_7,
    _id_ctrl_decoder_decoded_orMatrixOutputs_T_5,_id_ctrl_decoder_decoded_orMatrixOutputs_T_4,
    _id_ctrl_decoder_decoded_orMatrixOutputs_T_3,_id_ctrl_decoder_decoded_orMatrixOutputs_T_2,
    _id_ctrl_decoder_decoded_orMatrixOutputs_T_1,1'h0}; // @[Cat.scala 31:58]
  wire [19:0] id_ctrl_decoder_decoded_orMatrixOutputs_lo_17 = {_id_ctrl_decoder_decoded_orMatrixOutputs_T_19,1'h0,
    _id_ctrl_decoder_decoded_orMatrixOutputs_T_17,_id_ctrl_decoder_decoded_orMatrixOutputs_T_16,
    _id_ctrl_decoder_decoded_orMatrixOutputs_T_14,_id_ctrl_decoder_decoded_orMatrixOutputs_T_12,1'h0,1'h0,2'h0,
    id_ctrl_decoder_decoded_orMatrixOutputs_lo_lo_10}; // @[Cat.scala 31:58]
  wire [9:0] id_ctrl_decoder_decoded_orMatrixOutputs_hi_lo_11 = {_id_ctrl_decoder_decoded_orMatrixOutputs_T_39,
    _id_ctrl_decoder_decoded_orMatrixOutputs_T_37,_id_ctrl_decoder_decoded_orMatrixOutputs_T_35,
    _id_ctrl_decoder_decoded_orMatrixOutputs_T_33,_id_ctrl_decoder_decoded_orMatrixOutputs_T_31,
    _id_ctrl_decoder_decoded_orMatrixOutputs_T_29,_id_ctrl_decoder_decoded_orMatrixOutputs_T_27,
    _id_ctrl_decoder_decoded_orMatrixOutputs_T_25,_id_ctrl_decoder_decoded_orMatrixOutputs_T_23,
    _id_ctrl_decoder_decoded_orMatrixOutputs_T_21}; // @[Cat.scala 31:58]
  wire [4:0] id_ctrl_decoder_decoded_orMatrixOutputs_hi_hi_lo_6 = {_id_ctrl_decoder_decoded_orMatrixOutputs_T_47,
    _id_ctrl_decoder_decoded_orMatrixOutputs_T_37,1'h0,_id_ctrl_decoder_decoded_orMatrixOutputs_T_43,
    _id_ctrl_decoder_decoded_orMatrixOutputs_T_41}; // @[Cat.scala 31:58]
  wire [40:0] id_ctrl_decoder_decoded_orMatrixOutputs = {_id_ctrl_decoder_decoded_orMatrixOutputs_T_53,1'h0,1'h0,
    _id_ctrl_decoder_decoded_orMatrixOutputs_T_51,_id_ctrl_decoder_decoded_orMatrixOutputs_T_49,
    _id_ctrl_decoder_decoded_orMatrixOutputs_T_48,id_ctrl_decoder_decoded_orMatrixOutputs_hi_hi_lo_6,
    id_ctrl_decoder_decoded_orMatrixOutputs_hi_lo_11,id_ctrl_decoder_decoded_orMatrixOutputs_lo_17}; // @[Cat.scala 31:58]
  wire [9:0] id_ctrl_decoder_decoded_invMatrixOutputs_lo_lo = {id_ctrl_decoder_decoded_orMatrixOutputs[9],
    id_ctrl_decoder_decoded_orMatrixOutputs[8],id_ctrl_decoder_decoded_orMatrixOutputs[7],
    id_ctrl_decoder_decoded_orMatrixOutputs[6],id_ctrl_decoder_decoded_orMatrixOutputs[5],
    id_ctrl_decoder_decoded_orMatrixOutputs[4],id_ctrl_decoder_decoded_orMatrixOutputs[3],
    id_ctrl_decoder_decoded_orMatrixOutputs[2],id_ctrl_decoder_decoded_orMatrixOutputs[1],
    id_ctrl_decoder_decoded_orMatrixOutputs[0]}; // @[Cat.scala 31:58]
  wire [9:0] id_ctrl_decoder_decoded_invMatrixOutputs_lo_hi = {id_ctrl_decoder_decoded_orMatrixOutputs[19],
    id_ctrl_decoder_decoded_orMatrixOutputs[18],id_ctrl_decoder_decoded_orMatrixOutputs[17],
    id_ctrl_decoder_decoded_orMatrixOutputs[16],id_ctrl_decoder_decoded_orMatrixOutputs[15],
    id_ctrl_decoder_decoded_orMatrixOutputs[14],id_ctrl_decoder_decoded_orMatrixOutputs[13],
    id_ctrl_decoder_decoded_orMatrixOutputs[12],id_ctrl_decoder_decoded_orMatrixOutputs[11],
    id_ctrl_decoder_decoded_orMatrixOutputs[10]}; // @[Cat.scala 31:58]
  wire [9:0] id_ctrl_decoder_decoded_invMatrixOutputs_hi_lo = {id_ctrl_decoder_decoded_orMatrixOutputs[29],
    id_ctrl_decoder_decoded_orMatrixOutputs[28],id_ctrl_decoder_decoded_orMatrixOutputs[27],
    id_ctrl_decoder_decoded_orMatrixOutputs[26],id_ctrl_decoder_decoded_orMatrixOutputs[25],
    id_ctrl_decoder_decoded_orMatrixOutputs[24],id_ctrl_decoder_decoded_orMatrixOutputs[23],
    id_ctrl_decoder_decoded_orMatrixOutputs[22],id_ctrl_decoder_decoded_orMatrixOutputs[21],
    id_ctrl_decoder_decoded_orMatrixOutputs[20]}; // @[Cat.scala 31:58]
  wire [4:0] id_ctrl_decoder_decoded_invMatrixOutputs_hi_hi_lo = {id_ctrl_decoder_decoded_orMatrixOutputs[34],
    id_ctrl_decoder_decoded_orMatrixOutputs[33],id_ctrl_decoder_decoded_orMatrixOutputs[32],
    id_ctrl_decoder_decoded_orMatrixOutputs[31],id_ctrl_decoder_decoded_orMatrixOutputs[30]}; // @[Cat.scala 31:58]
  wire [40:0] id_ctrl_decoder_decoded_invMatrixOutputs = {id_ctrl_decoder_decoded_orMatrixOutputs[40],
    id_ctrl_decoder_decoded_orMatrixOutputs[39],id_ctrl_decoder_decoded_orMatrixOutputs[38],
    id_ctrl_decoder_decoded_orMatrixOutputs[37],id_ctrl_decoder_decoded_orMatrixOutputs[36],
    id_ctrl_decoder_decoded_orMatrixOutputs[35],id_ctrl_decoder_decoded_invMatrixOutputs_hi_hi_lo,
    id_ctrl_decoder_decoded_invMatrixOutputs_hi_lo,id_ctrl_decoder_decoded_invMatrixOutputs_lo_hi,
    id_ctrl_decoder_decoded_invMatrixOutputs_lo_lo}; // @[Cat.scala 31:58]
  wire  id_ctrl_decoder_0 = id_ctrl_decoder_decoded_invMatrixOutputs[40]; // @[Decode.scala 50:77]
  wire  id_ctrl_decoder_1 = id_ctrl_decoder_decoded_invMatrixOutputs[39]; // @[Decode.scala 50:77]
  wire  id_ctrl_decoder_2 = id_ctrl_decoder_decoded_invMatrixOutputs[38]; // @[Decode.scala 50:77]
  wire  id_ctrl_decoder_3 = id_ctrl_decoder_decoded_invMatrixOutputs[37]; // @[Decode.scala 50:77]
  wire  id_ctrl_decoder_4 = id_ctrl_decoder_decoded_invMatrixOutputs[36]; // @[Decode.scala 50:77]
  wire  id_ctrl_decoder_5 = id_ctrl_decoder_decoded_invMatrixOutputs[35]; // @[Decode.scala 50:77]
  wire  id_ctrl_decoder_6 = id_ctrl_decoder_decoded_invMatrixOutputs[34]; // @[Decode.scala 50:77]
  wire  id_ctrl_decoder_7 = id_ctrl_decoder_decoded_invMatrixOutputs[33]; // @[Decode.scala 50:77]
  wire  id_ctrl_decoder_8 = id_ctrl_decoder_decoded_invMatrixOutputs[32]; // @[Decode.scala 50:77]
  wire [1:0] id_ctrl_decoder_9 = id_ctrl_decoder_decoded_invMatrixOutputs[31:30]; // @[Decode.scala 50:77]
  wire [1:0] id_ctrl_decoder_10 = id_ctrl_decoder_decoded_invMatrixOutputs[29:28]; // @[Decode.scala 50:77]
  wire [2:0] id_ctrl_decoder_11 = id_ctrl_decoder_decoded_invMatrixOutputs[27:25]; // @[Decode.scala 50:77]
  wire [3:0] id_ctrl_decoder_13 = id_ctrl_decoder_decoded_invMatrixOutputs[23:20]; // @[Decode.scala 50:77]
  wire  id_ctrl_decoder_14 = id_ctrl_decoder_decoded_invMatrixOutputs[19]; // @[Decode.scala 50:77]
  wire [4:0] id_ctrl_decoder_15 = id_ctrl_decoder_decoded_invMatrixOutputs[18:14]; // @[Decode.scala 50:77]
  wire  id_ctrl_decoder_16 = id_ctrl_decoder_decoded_invMatrixOutputs[13]; // @[Decode.scala 50:77]
  wire  id_ctrl_decoder_17 = id_ctrl_decoder_decoded_invMatrixOutputs[12]; // @[Decode.scala 50:77]
  wire  id_ctrl_decoder_19 = id_ctrl_decoder_decoded_invMatrixOutputs[10]; // @[Decode.scala 50:77]
  wire  id_ctrl_decoder_20 = id_ctrl_decoder_decoded_invMatrixOutputs[9]; // @[Decode.scala 50:77]
  wire  id_ctrl_decoder_21 = id_ctrl_decoder_decoded_invMatrixOutputs[8]; // @[Decode.scala 50:77]
  wire  id_ctrl_decoder_22 = id_ctrl_decoder_decoded_invMatrixOutputs[7]; // @[Decode.scala 50:77]
  wire [2:0] id_ctrl_decoder_23 = id_ctrl_decoder_decoded_invMatrixOutputs[6:4]; // @[Decode.scala 50:77]
  wire  id_ctrl_decoder_24 = id_ctrl_decoder_decoded_invMatrixOutputs[3]; // @[Decode.scala 50:77]
  wire  id_ctrl_decoder_25 = id_ctrl_decoder_decoded_invMatrixOutputs[2]; // @[Decode.scala 50:77]
  wire  id_ctrl_decoder_26 = id_ctrl_decoder_decoded_invMatrixOutputs[1]; // @[Decode.scala 50:77]
  wire  id_ctrl_decoder_27 = id_ctrl_decoder_decoded_invMatrixOutputs[0]; // @[Decode.scala 50:77]
  wire [4:0] id_raddr2 = ibuf_io_inst_0_bits_inst_rs2; // @[RocketCore.scala 278:72]
  wire [4:0] id_raddr1 = ibuf_io_inst_0_bits_inst_rs1; // @[RocketCore.scala 278:72]
  wire [4:0] id_waddr = ibuf_io_inst_0_bits_inst_rd; // @[RocketCore.scala 278:72]
  reg  id_reg_fence; // @[RocketCore.scala 285:25]
  wire [31:0] _id_rs_T_4 = rf_id_rs_MPORT_data; // @[RocketCore.scala 1071:25]
  wire [31:0] _id_rs_T_9 = rf_id_rs_MPORT_1_data; // @[RocketCore.scala 1071:25]
  wire  _id_csr_en_T = id_ctrl_decoder_23 == 3'h6; // @[package.scala 15:47]
  wire  _id_csr_en_T_1 = id_ctrl_decoder_23 == 3'h7; // @[package.scala 15:47]
  wire  _id_csr_en_T_2 = id_ctrl_decoder_23 == 3'h5; // @[package.scala 15:47]
  wire  _id_csr_en_T_3 = _id_csr_en_T | _id_csr_en_T_1; // @[package.scala 72:59]
  wire  id_csr_en = _id_csr_en_T | _id_csr_en_T_1 | _id_csr_en_T_2; // @[package.scala 72:59]
  wire  id_system_insn = id_ctrl_decoder_23 == 3'h4; // @[RocketCore.scala 295:36]
  wire  id_csr_ren = _id_csr_en_T_3 & ibuf_io_inst_0_bits_inst_rs1 == 5'h0; // @[RocketCore.scala 296:54]
  wire  _id_csr_flush_T = ~id_csr_ren; // @[RocketCore.scala 298:54]
  wire  id_csr_flush = id_system_insn | id_csr_en & ~id_csr_ren & csr_io_decode_0_write_flush; // @[RocketCore.scala 298:37]
  wire  _id_illegal_insn_T_4 = (id_ctrl_decoder_20 | id_ctrl_decoder_21) & ~csr_io_status_isa[12]; // @[RocketCore.scala 307:34]
  wire  _id_illegal_insn_T_5 = ~id_ctrl_decoder_0 | _id_illegal_insn_T_4; // @[RocketCore.scala 306:40]
  wire  _id_illegal_insn_T_8 = id_ctrl_decoder_26 & ~csr_io_status_isa[0]; // @[RocketCore.scala 308:17]
  wire  _id_illegal_insn_T_9 = _id_illegal_insn_T_5 | _id_illegal_insn_T_8; // @[RocketCore.scala 307:65]
  wire  _id_illegal_insn_T_11 = id_ctrl_decoder_1 & csr_io_decode_0_fp_illegal; // @[RocketCore.scala 309:16]
  wire  _id_illegal_insn_T_12 = _id_illegal_insn_T_9 | _id_illegal_insn_T_11; // @[RocketCore.scala 308:48]
  wire  _id_illegal_insn_T_15 = id_ctrl_decoder_27 & ~csr_io_status_isa[3]; // @[RocketCore.scala 310:16]
  wire  _id_illegal_insn_T_16 = _id_illegal_insn_T_12 | _id_illegal_insn_T_15; // @[RocketCore.scala 309:70]
  wire  _id_illegal_insn_T_18 = ~csr_io_status_isa[2]; // @[RocketCore.scala 311:33]
  wire  _id_illegal_insn_T_19 = ibuf_io_inst_0_bits_rvc & ~csr_io_status_isa[2]; // @[RocketCore.scala 311:30]
  wire  _id_illegal_insn_T_20 = _id_illegal_insn_T_16 | _id_illegal_insn_T_19; // @[RocketCore.scala 310:47]
  wire  _id_illegal_insn_T_33 = id_ctrl_decoder_2 & csr_io_decode_0_rocc_illegal; // @[RocketCore.scala 315:18]
  wire  _id_illegal_insn_T_34 = _id_illegal_insn_T_20 | _id_illegal_insn_T_33; // @[RocketCore.scala 314:54]
  wire  _id_illegal_insn_T_38 = _id_illegal_insn_T_34 | id_ctrl_decoder_8; // @[RocketCore.scala 315:51]
  wire  _id_illegal_insn_T_42 = id_csr_en & (csr_io_decode_0_read_illegal | _id_csr_flush_T &
    csr_io_decode_0_write_illegal); // @[RocketCore.scala 317:15]
  wire  _id_illegal_insn_T_43 = _id_illegal_insn_T_38 | _id_illegal_insn_T_42; // @[RocketCore.scala 316:81]
  wire  _id_illegal_insn_T_46 = ~ibuf_io_inst_0_bits_rvc & (id_system_insn & csr_io_decode_0_system_illegal); // @[RocketCore.scala 318:31]
  wire  id_illegal_insn = _id_illegal_insn_T_43 | _id_illegal_insn_T_46; // @[RocketCore.scala 317:99]
  wire  id_amo_aq = ibuf_io_inst_0_bits_inst_bits[26]; // @[RocketCore.scala 323:29]
  wire  id_amo_rl = ibuf_io_inst_0_bits_inst_bits[25]; // @[RocketCore.scala 324:29]
  wire [3:0] id_fence_succ = ibuf_io_inst_0_bits_inst_bits[23:20]; // @[RocketCore.scala 326:33]
  wire  id_fence_next = id_ctrl_decoder_25 | id_ctrl_decoder_26 & id_amo_aq; // @[RocketCore.scala 327:37]
  wire  id_mem_busy = ~io_dmem_ordered | io_dmem_req_valid; // @[RocketCore.scala 328:38]
  wire  _GEN_0 = ~id_mem_busy ? 1'h0 : id_reg_fence; // @[RocketCore.scala 329:23 285:25 329:38]
  wire  id_do_fence_x9 = id_mem_busy & (id_ctrl_decoder_26 & id_amo_rl | id_ctrl_decoder_24 | id_reg_fence & (
    id_ctrl_decoder_14 | id_ctrl_decoder_2)); // @[RocketCore.scala 334:17]
  wire  id_xcpt = csr_io_interrupt | bpu_io_debug_if | bpu_io_xcpt_if | ibuf_io_inst_0_bits_xcpt0_ae_inst |
    ibuf_io_inst_0_bits_xcpt1_pf_inst | ibuf_io_inst_0_bits_xcpt1_gf_inst | ibuf_io_inst_0_bits_xcpt1_ae_inst |
    id_illegal_insn; // @[RocketCore.scala 1024:26]
  wire [4:0] _T_11 = ibuf_io_inst_0_bits_xcpt1_ae_inst ? 5'h1 : 5'h2; // @[Mux.scala 47:70]
  wire [4:0] _T_12 = ibuf_io_inst_0_bits_xcpt1_gf_inst ? 5'h14 : _T_11; // @[Mux.scala 47:70]
  wire [4:0] _T_13 = ibuf_io_inst_0_bits_xcpt1_pf_inst ? 5'hc : _T_12; // @[Mux.scala 47:70]
  wire [4:0] _T_14 = ibuf_io_inst_0_bits_xcpt0_ae_inst ? 5'h1 : _T_13; // @[Mux.scala 47:70]
  wire [4:0] _T_17 = bpu_io_xcpt_if ? 5'h3 : _T_14; // @[Mux.scala 47:70]
  wire [4:0] _T_18 = bpu_io_debug_if ? 5'he : _T_17; // @[Mux.scala 47:70]
  wire [4:0] ex_waddr = ex_reg_inst[11:7]; // @[RocketCore.scala 375:29]
  wire [4:0] mem_waddr = mem_reg_inst[11:7]; // @[RocketCore.scala 376:31]
  wire [4:0] wb_waddr = wb_reg_inst[11:7]; // @[RocketCore.scala 377:29]
  wire  _T_27 = ex_reg_valid & ex_ctrl_wxd; // @[RocketCore.scala 380:19]
  wire  _T_28 = mem_reg_valid & mem_ctrl_wxd; // @[RocketCore.scala 381:20]
  wire  _T_30 = mem_reg_valid & mem_ctrl_wxd & ~mem_ctrl_mem; // @[RocketCore.scala 381:36]
  wire  id_bypass_src_0_0 = 5'h0 == id_raddr1; // @[RocketCore.scala 383:82]
  wire  id_bypass_src_0_1 = _T_27 & ex_waddr == id_raddr1; // @[RocketCore.scala 383:74]
  wire  id_bypass_src_0_2 = _T_30 & mem_waddr == id_raddr1; // @[RocketCore.scala 383:74]
  wire  id_bypass_src_0_3 = _T_28 & mem_waddr == id_raddr1; // @[RocketCore.scala 383:74]
  wire  id_bypass_src_1_0 = 5'h0 == id_raddr2; // @[RocketCore.scala 383:82]
  wire  id_bypass_src_1_1 = _T_27 & ex_waddr == id_raddr2; // @[RocketCore.scala 383:74]
  wire  id_bypass_src_1_2 = _T_30 & mem_waddr == id_raddr2; // @[RocketCore.scala 383:74]
  wire  id_bypass_src_1_3 = _T_28 & mem_waddr == id_raddr2; // @[RocketCore.scala 383:74]
  reg  ex_reg_rs_bypass_0; // @[RocketCore.scala 387:29]
  reg  ex_reg_rs_bypass_1; // @[RocketCore.scala 387:29]
  reg [1:0] ex_reg_rs_lsb_0; // @[RocketCore.scala 388:26]
  reg [1:0] ex_reg_rs_lsb_1; // @[RocketCore.scala 388:26]
  reg [29:0] ex_reg_rs_msb_0; // @[RocketCore.scala 389:26]
  reg [29:0] ex_reg_rs_msb_1; // @[RocketCore.scala 389:26]
  wire [31:0] _ex_rs_T_1 = ex_reg_rs_lsb_0 == 2'h1 ? mem_reg_wdata : 32'h0; // @[package.scala 32:76]
  wire [31:0] _ex_rs_T_3 = ex_reg_rs_lsb_0 == 2'h2 ? wb_reg_wdata : _ex_rs_T_1; // @[package.scala 32:76]
  wire [31:0] _ex_rs_T_5 = ex_reg_rs_lsb_0 == 2'h3 ? io_dmem_resp_bits_data_word_bypass : _ex_rs_T_3; // @[package.scala 32:76]
  wire [31:0] _ex_rs_T_6 = {ex_reg_rs_msb_0,ex_reg_rs_lsb_0}; // @[Cat.scala 31:58]
  wire [31:0] _ex_rs_T_8 = ex_reg_rs_lsb_1 == 2'h1 ? mem_reg_wdata : 32'h0; // @[package.scala 32:76]
  wire [31:0] _ex_rs_T_10 = ex_reg_rs_lsb_1 == 2'h2 ? wb_reg_wdata : _ex_rs_T_8; // @[package.scala 32:76]
  wire [31:0] _ex_rs_T_12 = ex_reg_rs_lsb_1 == 2'h3 ? io_dmem_resp_bits_data_word_bypass : _ex_rs_T_10; // @[package.scala 32:76]
  wire [31:0] _ex_rs_T_13 = {ex_reg_rs_msb_1,ex_reg_rs_lsb_1}; // @[Cat.scala 31:58]
  wire [31:0] ex_rs_1 = ex_reg_rs_bypass_1 ? _ex_rs_T_12 : _ex_rs_T_13; // @[RocketCore.scala 391:14]
  wire  _ex_imm_sign_T = ex_ctrl_sel_imm == 3'h5; // @[RocketCore.scala 1086:24]
  wire  _ex_imm_sign_T_2 = ex_reg_inst[31]; // @[RocketCore.scala 1086:53]
  wire  ex_imm_sign = ex_ctrl_sel_imm == 3'h5 ? $signed(1'sh0) : $signed(_ex_imm_sign_T_2); // @[RocketCore.scala 1086:19]
  wire  _ex_imm_b30_20_T = ex_ctrl_sel_imm == 3'h2; // @[RocketCore.scala 1087:26]
  wire [10:0] _ex_imm_b30_20_T_2 = ex_reg_inst[30:20]; // @[RocketCore.scala 1087:49]
  wire [7:0] _ex_imm_b19_12_T_4 = ex_reg_inst[19:12]; // @[RocketCore.scala 1088:73]
  wire  _ex_imm_b11_T_2 = _ex_imm_b30_20_T | _ex_imm_sign_T; // @[RocketCore.scala 1089:33]
  wire  _ex_imm_b11_T_5 = ex_reg_inst[20]; // @[RocketCore.scala 1090:44]
  wire  _ex_imm_b11_T_6 = ex_ctrl_sel_imm == 3'h1; // @[RocketCore.scala 1091:23]
  wire  _ex_imm_b11_T_8 = ex_reg_inst[7]; // @[RocketCore.scala 1091:43]
  wire  _ex_imm_b11_T_9 = ex_ctrl_sel_imm == 3'h1 ? $signed(_ex_imm_b11_T_8) : $signed(ex_imm_sign); // @[RocketCore.scala 1091:18]
  wire  _ex_imm_b11_T_10 = ex_ctrl_sel_imm == 3'h3 ? $signed(_ex_imm_b11_T_5) : $signed(_ex_imm_b11_T_9); // @[RocketCore.scala 1090:18]
  wire [5:0] ex_imm_b10_5 = _ex_imm_b11_T_2 ? 6'h0 : ex_reg_inst[30:25]; // @[RocketCore.scala 1092:20]
  wire  _ex_imm_b4_1_T_1 = ex_ctrl_sel_imm == 3'h0; // @[RocketCore.scala 1094:24]
  wire [3:0] _ex_imm_b4_1_T_8 = _ex_imm_sign_T ? ex_reg_inst[19:16] : ex_reg_inst[24:21]; // @[RocketCore.scala 1095:19]
  wire [3:0] _ex_imm_b4_1_T_9 = ex_ctrl_sel_imm == 3'h0 | _ex_imm_b11_T_6 ? ex_reg_inst[11:8] : _ex_imm_b4_1_T_8; // @[RocketCore.scala 1094:19]
  wire [3:0] ex_imm_b4_1 = _ex_imm_b30_20_T ? 4'h0 : _ex_imm_b4_1_T_9; // @[RocketCore.scala 1093:19]
  wire  _ex_imm_b0_T_6 = _ex_imm_sign_T & ex_reg_inst[15]; // @[RocketCore.scala 1098:17]
  wire  _ex_imm_b0_T_7 = ex_ctrl_sel_imm == 3'h4 ? ex_reg_inst[20] : _ex_imm_b0_T_6; // @[RocketCore.scala 1097:17]
  wire  ex_imm_b0 = _ex_imm_b4_1_T_1 ? ex_reg_inst[7] : _ex_imm_b0_T_7; // @[RocketCore.scala 1096:17]
  wire  ex_imm_hi_lo_lo = _ex_imm_b30_20_T | _ex_imm_sign_T ? $signed(1'sh0) : $signed(_ex_imm_b11_T_10); // @[Cat.scala 31:58]
  wire [7:0] ex_imm_hi_lo_hi = ex_ctrl_sel_imm != 3'h2 & ex_ctrl_sel_imm != 3'h3 ? $signed({8{ex_imm_sign}}) : $signed(
    _ex_imm_b19_12_T_4); // @[Cat.scala 31:58]
  wire [10:0] ex_imm_hi_hi_lo = ex_ctrl_sel_imm == 3'h2 ? $signed(_ex_imm_b30_20_T_2) : $signed({11{ex_imm_sign}}); // @[Cat.scala 31:58]
  wire  ex_imm_hi_hi_hi = ex_ctrl_sel_imm == 3'h5 ? $signed(1'sh0) : $signed(_ex_imm_sign_T_2); // @[Cat.scala 31:58]
  wire [31:0] ex_imm = {ex_imm_hi_hi_hi,ex_imm_hi_hi_lo,ex_imm_hi_lo_hi,ex_imm_hi_lo_lo,ex_imm_b10_5,ex_imm_b4_1,
    ex_imm_b0}; // @[RocketCore.scala 1100:53]
  wire [31:0] _ex_op1_T = ex_reg_rs_bypass_0 ? _ex_rs_T_5 : _ex_rs_T_6; // @[RocketCore.scala 394:24]
  wire [31:0] _ex_op1_T_3 = 2'h1 == ex_ctrl_sel_alu1 ? $signed(_ex_op1_T) : $signed(32'sh0); // @[Mux.scala 81:58]
  wire [31:0] _ex_op2_T = ex_reg_rs_bypass_1 ? _ex_rs_T_12 : _ex_rs_T_13; // @[RocketCore.scala 397:24]
  wire [3:0] _ex_op2_T_1 = ex_reg_rvc ? $signed(4'sh2) : $signed(4'sh4); // @[RocketCore.scala 399:19]
  wire [31:0] _ex_op2_T_3 = 2'h2 == ex_ctrl_sel_alu2 ? $signed(_ex_op2_T) : $signed(32'sh0); // @[Mux.scala 81:58]
  wire [31:0] _ex_op2_T_5 = 2'h3 == ex_ctrl_sel_alu2 ? $signed(ex_imm) : $signed(_ex_op2_T_3); // @[Mux.scala 81:58]
  wire  _T_134 = id_raddr1 != 5'h0; // @[RocketCore.scala 759:55]
  wire  _T_135 = id_ctrl_decoder_7 & id_raddr1 != 5'h0; // @[RocketCore.scala 759:42]
  wire  _data_hazard_ex_T = id_raddr1 == ex_waddr; // @[RocketCore.scala 779:70]
  wire  _T_136 = id_raddr2 != 5'h0; // @[RocketCore.scala 760:55]
  wire  _T_137 = id_ctrl_decoder_6 & id_raddr2 != 5'h0; // @[RocketCore.scala 760:42]
  wire  _data_hazard_ex_T_2 = id_raddr2 == ex_waddr; // @[RocketCore.scala 779:70]
  wire  _T_139 = id_ctrl_decoder_22 & id_waddr != 5'h0; // @[RocketCore.scala 761:42]
  wire  _data_hazard_ex_T_4 = id_waddr == ex_waddr; // @[RocketCore.scala 779:70]
  wire  _data_hazard_ex_T_7 = _T_135 & _data_hazard_ex_T | _T_137 & _data_hazard_ex_T_2 | _T_139 & _data_hazard_ex_T_4; // @[RocketCore.scala 1033:50]
  wire  data_hazard_ex = ex_ctrl_wxd & _data_hazard_ex_T_7; // @[RocketCore.scala 779:36]
  wire  ex_cannot_bypass = ex_ctrl_csr != 3'h0 | ex_ctrl_jalr | ex_ctrl_mem | ex_ctrl_mul | ex_ctrl_div | ex_ctrl_fp |
    ex_ctrl_rocc; // @[RocketCore.scala 778:123]
  wire  id_ex_hazard = ex_reg_valid & (data_hazard_ex & ex_cannot_bypass); // @[RocketCore.scala 781:35]
  wire  _data_hazard_mem_T = id_raddr1 == mem_waddr; // @[RocketCore.scala 788:72]
  wire  _data_hazard_mem_T_2 = id_raddr2 == mem_waddr; // @[RocketCore.scala 788:72]
  wire  _data_hazard_mem_T_4 = id_waddr == mem_waddr; // @[RocketCore.scala 788:72]
  wire  _data_hazard_mem_T_7 = _T_135 & _data_hazard_mem_T | _T_137 & _data_hazard_mem_T_2 | _T_139 &
    _data_hazard_mem_T_4; // @[RocketCore.scala 1033:50]
  wire  data_hazard_mem = mem_ctrl_wxd & _data_hazard_mem_T_7; // @[RocketCore.scala 788:38]
  wire  mem_cannot_bypass = mem_ctrl_csr != 3'h0 | mem_ctrl_mem & mem_reg_slow_bypass | mem_ctrl_mul | mem_ctrl_div |
    mem_ctrl_fp | mem_ctrl_rocc; // @[RocketCore.scala 787:131]
  wire  id_mem_hazard = mem_reg_valid & (data_hazard_mem & mem_cannot_bypass); // @[RocketCore.scala 790:37]
  wire  _data_hazard_wb_T = id_raddr1 == wb_waddr; // @[RocketCore.scala 794:70]
  wire  _data_hazard_wb_T_2 = id_raddr2 == wb_waddr; // @[RocketCore.scala 794:70]
  wire  _data_hazard_wb_T_4 = id_waddr == wb_waddr; // @[RocketCore.scala 794:70]
  wire  _data_hazard_wb_T_7 = _T_135 & _data_hazard_wb_T | _T_137 & _data_hazard_wb_T_2 | _T_139 & _data_hazard_wb_T_4; // @[RocketCore.scala 1033:50]
  wire  data_hazard_wb = wb_ctrl_wxd & _data_hazard_wb_T_7; // @[RocketCore.scala 794:36]
  wire  wb_dcache_miss = wb_ctrl_mem & ~io_dmem_resp_valid; // @[RocketCore.scala 511:36]
  wire  wb_set_sboard = wb_ctrl_div | wb_dcache_miss | wb_ctrl_rocc; // @[RocketCore.scala 665:53]
  wire  id_wb_hazard = wb_reg_valid & (data_hazard_wb & wb_set_sboard); // @[RocketCore.scala 796:35]
  reg [31:0] _r; // @[RocketCore.scala 1050:25]
  wire [31:0] r = {_r[31:1], 1'h0}; // @[RocketCore.scala 1051:40]
  wire [31:0] _id_sboard_hazard_T = r >> id_raddr1; // @[RocketCore.scala 1047:35]
  wire  dmem_resp_valid = io_dmem_resp_valid & io_dmem_resp_bits_has_data; // @[RocketCore.scala 675:44]
  wire  dmem_resp_replay = dmem_resp_valid & io_dmem_resp_bits_replay; // @[RocketCore.scala 676:42]
  wire  dmem_resp_xpu = ~io_dmem_resp_bits_tag[0]; // @[RocketCore.scala 672:23]
  wire  ll_wen_x2 = div_io_resp_ready & div_io_resp_valid; // @[Decoupled.scala 50:35]
  wire  ll_wen = dmem_resp_replay & dmem_resp_xpu | ll_wen_x2; // @[RocketCore.scala 691:44 696:12]
  wire [4:0] dmem_resp_waddr = io_dmem_resp_bits_tag[5:1]; // @[RocketCore.scala 674:46]
  wire [4:0] ll_waddr = dmem_resp_replay & dmem_resp_xpu ? dmem_resp_waddr : div_io_resp_bits_tag; // @[RocketCore.scala 691:44 695:14]
  wire  _id_sboard_hazard_T_3 = ll_wen & ll_waddr == id_raddr1; // @[RocketCore.scala 771:58]
  wire  _id_sboard_hazard_T_5 = _id_sboard_hazard_T[0] & ~_id_sboard_hazard_T_3; // @[RocketCore.scala 774:77]
  wire [31:0] _id_sboard_hazard_T_7 = r >> id_raddr2; // @[RocketCore.scala 1047:35]
  wire  _id_sboard_hazard_T_10 = ll_wen & ll_waddr == id_raddr2; // @[RocketCore.scala 771:58]
  wire  _id_sboard_hazard_T_12 = _id_sboard_hazard_T_7[0] & ~_id_sboard_hazard_T_10; // @[RocketCore.scala 774:77]
  wire [31:0] _id_sboard_hazard_T_14 = r >> id_waddr; // @[RocketCore.scala 1047:35]
  wire  _id_sboard_hazard_T_17 = ll_wen & ll_waddr == id_waddr; // @[RocketCore.scala 771:58]
  wire  _id_sboard_hazard_T_19 = _id_sboard_hazard_T_14[0] & ~_id_sboard_hazard_T_17; // @[RocketCore.scala 774:77]
  wire  id_sboard_hazard = _T_135 & _id_sboard_hazard_T_5 | _T_137 & _id_sboard_hazard_T_12 | _T_139 &
    _id_sboard_hazard_T_19; // @[RocketCore.scala 1033:50]
  wire  _ctrl_stalld_T_5 = csr_io_singleStep & (ex_reg_valid | mem_reg_valid | wb_reg_valid); // @[RocketCore.scala 818:23]
  wire  _ctrl_stalld_T_6 = id_ex_hazard | id_mem_hazard | id_wb_hazard | id_sboard_hazard | _ctrl_stalld_T_5; // @[RocketCore.scala 817:71]
  reg  blocked; // @[RocketCore.scala 809:22]
  wire  _dcache_blocked_T = ~io_dmem_perf_grant; // @[RocketCore.scala 811:16]
  wire  dcache_blocked = blocked & ~io_dmem_perf_grant; // @[RocketCore.scala 811:13]
  wire  _ctrl_stalld_T_13 = id_ctrl_decoder_14 & dcache_blocked; // @[RocketCore.scala 821:17]
  wire  _ctrl_stalld_T_14 = _ctrl_stalld_T_6 | _ctrl_stalld_T_13; // @[RocketCore.scala 820:32]
  reg  rocc_blocked; // @[RocketCore.scala 813:25]
  wire  _ctrl_stalld_T_15 = id_ctrl_decoder_2 & rocc_blocked; // @[RocketCore.scala 822:18]
  wire  _ctrl_stalld_T_16 = _ctrl_stalld_T_14 | _ctrl_stalld_T_15; // @[RocketCore.scala 821:35]
  wire  wb_wxd = wb_reg_valid & wb_ctrl_wxd; // @[RocketCore.scala 664:29]
  wire  _ctrl_stalld_T_17 = ~wb_wxd; // @[RocketCore.scala 823:65]
  wire  _ctrl_stalld_T_22 = id_ctrl_decoder_21 & (~(div_io_req_ready | div_io_resp_valid & ~wb_wxd) | div_io_req_valid); // @[RocketCore.scala 823:17]
  wire  _ctrl_stalld_T_23 = _ctrl_stalld_T_16 | _ctrl_stalld_T_22; // @[RocketCore.scala 822:34]
  wire  _ctrl_stalld_T_26 = _ctrl_stalld_T_23 | id_do_fence_x9; // @[RocketCore.scala 824:15]
  wire  _ctrl_stalld_T_27 = _ctrl_stalld_T_26 | csr_io_csr_stall; // @[RocketCore.scala 825:17]
  wire  ctrl_stalld = _ctrl_stalld_T_27 | id_reg_pause; // @[RocketCore.scala 826:22]
  wire  ctrl_killd = ~ibuf_io_inst_0_valid | ibuf_io_inst_0_bits_replay | take_pc_mem_wb | ctrl_stalld |
    csr_io_interrupt; // @[RocketCore.scala 829:104]
  wire  _ex_reg_valid_T = ~ctrl_killd; // @[RocketCore.scala 439:19]
  wire  _ex_reg_replay_T = ~take_pc_mem_wb; // @[RocketCore.scala 440:20]
  wire  _ex_reg_replay_T_1 = ~take_pc_mem_wb & ibuf_io_inst_0_valid; // @[RocketCore.scala 440:29]
  wire  _GEN_1 = id_ctrl_decoder_25 & id_fence_succ == 4'h0 | id_reg_pause; // @[RocketCore.scala 117:25 450:{49,64}]
  wire  _GEN_2 = id_fence_next | _GEN_0; // @[RocketCore.scala 451:{26,41}]
  wire [2:0] _T_35 = {ibuf_io_inst_0_bits_xcpt1_pf_inst,ibuf_io_inst_0_bits_xcpt1_gf_inst,
    ibuf_io_inst_0_bits_xcpt1_ae_inst}; // @[RocketCore.scala 457:22]
  wire  _GEN_5 = |_T_35 | ibuf_io_inst_0_bits_rvc; // @[RocketCore.scala 446:16 457:34 460:20]
  wire [2:0] _T_37 = {2'h0,ibuf_io_inst_0_bits_xcpt0_ae_inst}; // @[RocketCore.scala 462:40]
  wire  _T_40 = id_ctrl_decoder_15 == 5'h14; // @[package.scala 15:47]
  wire  _T_41 = id_ctrl_decoder_15 == 5'h15; // @[package.scala 15:47]
  wire  _T_42 = id_ctrl_decoder_15 == 5'h16; // @[package.scala 15:47]
  wire  _T_43 = id_ctrl_decoder_15 == 5'h5; // @[package.scala 15:47]
  wire  _T_46 = _T_40 | _T_41 | _T_42 | _T_43; // @[package.scala 72:59]
  wire [1:0] _ex_reg_mem_size_T_6 = {_T_136,_T_134}; // @[Cat.scala 31:58]
  wire  do_bypass = id_bypass_src_0_0 | id_bypass_src_0_1 | id_bypass_src_0_2 | id_bypass_src_0_3; // @[RocketCore.scala 484:48]
  wire [1:0] _bypass_src_T = id_bypass_src_0_2 ? 2'h2 : 2'h3; // @[Mux.scala 47:70]
  wire [1:0] _bypass_src_T_1 = id_bypass_src_0_1 ? 2'h1 : _bypass_src_T; // @[Mux.scala 47:70]
  wire  _wb_valid_T_2 = ~wb_xcpt; // @[RocketCore.scala 699:48]
  wire  wb_valid = wb_reg_valid & ~replay_wb & ~wb_xcpt; // @[RocketCore.scala 699:45]
  wire  wb_wen = wb_valid & wb_ctrl_wxd; // @[RocketCore.scala 700:25]
  wire  rf_wen = wb_wen | ll_wen; // @[RocketCore.scala 701:23]
  wire [4:0] rf_waddr = ll_wen ? ll_waddr : wb_waddr; // @[RocketCore.scala 702:21]
  wire  _T_129 = rf_waddr != 5'h0; // @[RocketCore.scala 1076:16]
  wire  _rf_wdata_T = dmem_resp_valid & dmem_resp_xpu; // @[RocketCore.scala 703:38]
  wire [31:0] ll_wdata = div_io_resp_bits_data;
  wire [31:0] _rf_wdata_T_4 = wb_ctrl_csr != 3'h0 ? csr_io_rw_rdata : wb_reg_wdata; // @[RocketCore.scala 705:21]
  wire [31:0] _rf_wdata_T_5 = ll_wen ? ll_wdata : _rf_wdata_T_4; // @[RocketCore.scala 704:21]
  wire [31:0] rf_wdata = dmem_resp_valid & dmem_resp_xpu ? io_dmem_resp_bits_data : _rf_wdata_T_5; // @[RocketCore.scala 703:21]
  wire [31:0] _GEN_233 = rf_waddr == id_raddr1 ? rf_wdata : _id_rs_T_4; // @[RocketCore.scala 1071:19 1079:{31,39}]
  wire [31:0] _GEN_240 = rf_waddr != 5'h0 ? _GEN_233 : _id_rs_T_4; // @[RocketCore.scala 1071:19 1076:29]
  wire [31:0] id_rs_0 = rf_wen ? _GEN_240 : _id_rs_T_4; // @[RocketCore.scala 708:17 1071:19]
  wire  do_bypass_1 = id_bypass_src_1_0 | id_bypass_src_1_1 | id_bypass_src_1_2 | id_bypass_src_1_3; // @[RocketCore.scala 484:48]
  wire [1:0] _bypass_src_T_2 = id_bypass_src_1_2 ? 2'h2 : 2'h3; // @[Mux.scala 47:70]
  wire [31:0] _GEN_234 = rf_waddr == id_raddr2 ? rf_wdata : _id_rs_T_9; // @[RocketCore.scala 1071:19 1079:{31,39}]
  wire [31:0] _GEN_241 = rf_waddr != 5'h0 ? _GEN_234 : _id_rs_T_9; // @[RocketCore.scala 1071:19 1076:29]
  wire [31:0] id_rs_1 = rf_wen ? _GEN_241 : _id_rs_T_9; // @[RocketCore.scala 708:17 1071:19]
  wire [31:0] inst = ibuf_io_inst_0_bits_rvc ? {{16'd0}, ibuf_io_inst_0_bits_raw[15:0]} : ibuf_io_inst_0_bits_raw; // @[RocketCore.scala 494:21]
  wire  id_load_use = mem_reg_valid & data_hazard_mem & mem_ctrl_mem; // @[RocketCore.scala 791:51]
  wire  ex_pc_valid = ex_reg_valid | ex_reg_replay | ex_reg_xcpt_interrupt; // @[RocketCore.scala 510:51]
  wire  _replay_ex_structural_T = ~io_dmem_req_ready; // @[RocketCore.scala 512:45]
  wire  _replay_ex_structural_T_3 = ex_ctrl_div & ~div_io_req_ready; // @[RocketCore.scala 513:42]
  wire  replay_ex_structural = ex_ctrl_mem & ~io_dmem_req_ready | _replay_ex_structural_T_3; // @[RocketCore.scala 512:64]
  wire  replay_ex_load_use = wb_dcache_miss & ex_reg_load_use; // @[RocketCore.scala 514:43]
  wire  replay_ex = ex_reg_replay | ex_reg_valid & (replay_ex_structural | replay_ex_load_use); // @[RocketCore.scala 515:33]
  wire  ctrl_killx = take_pc_mem_wb | replay_ex | ~ex_reg_valid; // @[RocketCore.scala 516:48]
  wire  _ex_slow_bypass_T = ex_ctrl_mem_cmd == 5'h7; // @[RocketCore.scala 518:40]
  wire  ex_slow_bypass = ex_ctrl_mem_cmd == 5'h7 | ex_reg_mem_size < 2'h2; // @[RocketCore.scala 518:50]
  wire  ex_xcpt = ex_reg_xcpt_interrupt | ex_reg_xcpt; // @[RocketCore.scala 522:28]
  wire  mem_pc_valid = mem_reg_valid | mem_reg_replay | mem_reg_xcpt_interrupt; // @[RocketCore.scala 528:54]
  wire  mem_br_target_sign = mem_reg_inst[31]; // @[RocketCore.scala 1086:53]
  wire [5:0] mem_br_target_b10_5 = mem_reg_inst[30:25]; // @[RocketCore.scala 1092:66]
  wire [3:0] mem_br_target_b4_1 = mem_reg_inst[11:8]; // @[RocketCore.scala 1094:57]
  wire  mem_br_target_hi_lo_lo = mem_reg_inst[7]; // @[Cat.scala 31:58]
  wire [7:0] mem_br_target_hi_lo_hi = {8{mem_br_target_sign}}; // @[Cat.scala 31:58]
  wire [10:0] mem_br_target_hi_hi_lo = {11{mem_br_target_sign}}; // @[Cat.scala 31:58]
  wire  mem_br_target_hi_hi_hi = mem_reg_inst[31]; // @[Cat.scala 31:58]
  wire [31:0] _mem_br_target_T_3 = {mem_br_target_hi_hi_hi,mem_br_target_hi_hi_lo,mem_br_target_hi_lo_hi,
    mem_br_target_hi_lo_lo,mem_br_target_b10_5,mem_br_target_b4_1,1'h0}; // @[RocketCore.scala 1100:53]
  wire  mem_br_target_hi_lo_lo_1 = mem_reg_inst[20]; // @[Cat.scala 31:58]
  wire [7:0] mem_br_target_hi_lo_hi_1 = mem_reg_inst[19:12]; // @[Cat.scala 31:58]
  wire [31:0] _mem_br_target_T_5 = {mem_br_target_hi_hi_hi,mem_br_target_hi_hi_lo,mem_br_target_hi_lo_hi_1,
    mem_br_target_hi_lo_lo_1,mem_br_target_b10_5,mem_reg_inst[24:21],1'h0}; // @[RocketCore.scala 1100:53]
  wire [3:0] _mem_br_target_T_6 = mem_reg_rvc ? $signed(4'sh2) : $signed(4'sh4); // @[RocketCore.scala 532:8]
  wire [31:0] _mem_br_target_T_7 = mem_ctrl_jal ? $signed(_mem_br_target_T_5) : $signed({{28{_mem_br_target_T_6[3]}},
    _mem_br_target_T_6}); // @[RocketCore.scala 531:8]
  wire [31:0] _mem_br_target_T_8 = _mem_cfi_taken_T ? $signed(_mem_br_target_T_3) : $signed(_mem_br_target_T_7); // @[RocketCore.scala 530:8]
  wire [31:0] mem_br_target = $signed(mem_reg_pc) + $signed(_mem_br_target_T_8); // @[RocketCore.scala 529:41]
  wire [31:0] _mem_npc_T_2 = mem_ctrl_jalr ? $signed(mem_reg_wdata) : $signed(mem_br_target); // @[RocketCore.scala 533:21]
  wire [31:0] mem_npc = $signed(_mem_npc_T_2) & -32'sh2; // @[RocketCore.scala 533:141]
  wire  _mem_wrong_npc_T_3 = ibuf_io_inst_0_valid | ibuf_io_imem_valid ? mem_npc != ibuf_io_pc : 1'h1; // @[RocketCore.scala 536:8]
  wire  mem_wrong_npc = ex_pc_valid ? mem_npc != ex_reg_pc : _mem_wrong_npc_T_3; // @[RocketCore.scala 535:8]
  wire  mem_npc_misaligned = _id_illegal_insn_T_18 & mem_npc[1]; // @[RocketCore.scala 537:56]
  wire [31:0] mem_int_wdata = _take_pc_mem_T & (mem_ctrl_jalr ^ mem_npc_misaligned) ? $signed(mem_br_target) : $signed(
    mem_reg_wdata); // @[RocketCore.scala 538:119]
  wire  mem_cfi = mem_ctrl_branch | mem_ctrl_jalr | mem_ctrl_jal; // @[RocketCore.scala 539:50]
  wire  _mem_reg_valid_T = ~ctrl_killx; // @[RocketCore.scala 545:20]
  wire  _mem_reg_load_T = ex_ctrl_mem_cmd == 5'h0; // @[package.scala 15:47]
  wire  _mem_reg_load_T_1 = ex_ctrl_mem_cmd == 5'h10; // @[package.scala 15:47]
  wire  _mem_reg_load_T_2 = ex_ctrl_mem_cmd == 5'h6; // @[package.scala 15:47]
  wire  _mem_reg_load_T_6 = _mem_reg_load_T | _mem_reg_load_T_1 | _mem_reg_load_T_2 | _ex_slow_bypass_T; // @[package.scala 72:59]
  wire  _mem_reg_load_T_7 = ex_ctrl_mem_cmd == 5'h4; // @[package.scala 15:47]
  wire  _mem_reg_load_T_8 = ex_ctrl_mem_cmd == 5'h9; // @[package.scala 15:47]
  wire  _mem_reg_load_T_9 = ex_ctrl_mem_cmd == 5'ha; // @[package.scala 15:47]
  wire  _mem_reg_load_T_10 = ex_ctrl_mem_cmd == 5'hb; // @[package.scala 15:47]
  wire  _mem_reg_load_T_13 = _mem_reg_load_T_7 | _mem_reg_load_T_8 | _mem_reg_load_T_9 | _mem_reg_load_T_10; // @[package.scala 72:59]
  wire  _mem_reg_load_T_14 = ex_ctrl_mem_cmd == 5'h8; // @[package.scala 15:47]
  wire  _mem_reg_load_T_15 = ex_ctrl_mem_cmd == 5'hc; // @[package.scala 15:47]
  wire  _mem_reg_load_T_16 = ex_ctrl_mem_cmd == 5'hd; // @[package.scala 15:47]
  wire  _mem_reg_load_T_17 = ex_ctrl_mem_cmd == 5'he; // @[package.scala 15:47]
  wire  _mem_reg_load_T_18 = ex_ctrl_mem_cmd == 5'hf; // @[package.scala 15:47]
  wire  _mem_reg_load_T_22 = _mem_reg_load_T_14 | _mem_reg_load_T_15 | _mem_reg_load_T_16 | _mem_reg_load_T_17 |
    _mem_reg_load_T_18; // @[package.scala 72:59]
  wire  _mem_reg_load_T_23 = _mem_reg_load_T_13 | _mem_reg_load_T_22; // @[Consts.scala 83:44]
  wire  _mem_reg_load_T_24 = _mem_reg_load_T_6 | _mem_reg_load_T_23; // @[Consts.scala 85:68]
  wire  _mem_reg_store_T_22 = ex_ctrl_mem_cmd == 5'h1 | ex_ctrl_mem_cmd == 5'h11 | _ex_slow_bypass_T |
    _mem_reg_load_T_23; // @[Consts.scala 86:76]
  wire [31:0] _mem_reg_wdata_T = alu_io_out; // @[RocketCore.scala 573:25]
  wire [1:0] size = ex_ctrl_rocc ? 2'h2 : ex_reg_mem_size; // @[RocketCore.scala 577:21]
  wire [31:0] _mem_reg_rs2_T_3 = {ex_rs_1[7:0],ex_rs_1[7:0],ex_rs_1[7:0],ex_rs_1[7:0]}; // @[Cat.scala 31:58]
  wire [31:0] _mem_reg_rs2_T_6 = {ex_rs_1[15:0],ex_rs_1[15:0]}; // @[Cat.scala 31:58]
  wire [31:0] _mem_reg_rs2_T_7 = size == 2'h1 ? _mem_reg_rs2_T_6 : ex_rs_1; // @[AMOALU.scala 27:13]
  wire  _GEN_79 = ex_ctrl_jalr & csr_io_status_debug | ex_ctrl_fence_i; // @[RocketCore.scala 555:14 580:48 582:24]
  wire  _GEN_80 = ex_ctrl_jalr & csr_io_status_debug | ex_reg_flush_pipe; // @[RocketCore.scala 563:24 580:48 583:26]
  wire  mem_breakpoint = mem_reg_load & bpu_io_xcpt_ld | mem_reg_store & bpu_io_xcpt_st; // @[RocketCore.scala 587:57]
  wire  mem_debug_breakpoint = mem_reg_load & bpu_io_debug_ld | mem_reg_store & bpu_io_debug_st; // @[RocketCore.scala 588:64]
  wire  mem_ldst_xcpt = mem_debug_breakpoint | mem_breakpoint; // @[RocketCore.scala 1024:26]
  wire [3:0] mem_ldst_cause = mem_debug_breakpoint ? 4'he : 4'h3; // @[Mux.scala 47:70]
  wire  _T_70 = mem_reg_xcpt_interrupt | mem_reg_xcpt; // @[RocketCore.scala 594:29]
  wire  _T_71 = mem_reg_valid & mem_npc_misaligned; // @[RocketCore.scala 595:20]
  wire  _T_72 = mem_reg_valid & mem_ldst_xcpt; // @[RocketCore.scala 596:20]
  wire  mem_xcpt = _T_70 | _T_71 | _T_72; // @[RocketCore.scala 1024:26]
  wire [3:0] _T_74 = _T_71 ? 4'h0 : mem_ldst_cause; // @[Mux.scala 47:70]
  wire  dcache_kill_mem = _T_28 & io_dmem_replay_next; // @[RocketCore.scala 605:55]
  wire  replay_mem = dcache_kill_mem | mem_reg_replay; // @[RocketCore.scala 607:37]
  wire  killm_common = dcache_kill_mem | take_pc_wb | mem_reg_xcpt | ~mem_reg_valid; // @[RocketCore.scala 608:68]
  reg  div_io_kill_REG; // @[RocketCore.scala 609:37]
  wire  ctrl_killm = killm_common | mem_xcpt; // @[RocketCore.scala 610:33]
  wire  _wb_reg_valid_T = ~ctrl_killm; // @[RocketCore.scala 613:19]
  wire  _wb_reg_replay_T = ~take_pc_wb; // @[RocketCore.scala 614:34]
  wire [2:0] _T_113 = _T_103 ? 3'h6 : 3'h4; // @[Mux.scala 47:70]
  wire [2:0] _T_114 = _T_101 ? 3'h5 : _T_113; // @[Mux.scala 47:70]
  wire [2:0] _T_115 = _T_99 ? 3'h7 : _T_114; // @[Mux.scala 47:70]
  wire [4:0] _T_116 = {{2'd0}, _T_115}; // @[Mux.scala 47:70]
  wire [4:0] _T_118 = _T_93 ? 5'hd : _T_116; // @[Mux.scala 47:70]
  wire [4:0] _T_119 = _T_91 ? 5'hf : _T_118; // @[Mux.scala 47:70]
  wire [15:0] _csr_io_inst_0_T_3 = &wb_reg_raw_inst[1:0] ? wb_reg_inst[31:16] : 16'h0; // @[RocketCore.scala 716:50]
  wire [31:0] _io_fpu_time_T = csr_io_time; // @[RocketCore.scala 721:29]
  wire  tval_dmem_addr = ~wb_reg_xcpt; // @[RocketCore.scala 725:24]
  wire  _tval_any_addr_T = wb_reg_cause == 32'h3; // @[package.scala 15:47]
  wire  _tval_any_addr_T_1 = wb_reg_cause == 32'h1; // @[package.scala 15:47]
  wire  _tval_any_addr_T_2 = wb_reg_cause == 32'hc; // @[package.scala 15:47]
  wire  _tval_any_addr_T_3 = wb_reg_cause == 32'h14; // @[package.scala 15:47]
  wire  _tval_any_addr_T_6 = _tval_any_addr_T | _tval_any_addr_T_1 | _tval_any_addr_T_2 | _tval_any_addr_T_3; // @[package.scala 72:59]
  wire  tval_any_addr = tval_dmem_addr | _tval_any_addr_T_6; // @[RocketCore.scala 726:38]
  wire  tval_inst = wb_reg_cause == 32'h2; // @[RocketCore.scala 728:32]
  wire  tval_valid = wb_xcpt & (tval_any_addr | tval_inst); // @[RocketCore.scala 729:28]
  wire  htval_valid_imem = wb_reg_xcpt & _tval_any_addr_T_3; // @[RocketCore.scala 733:40]
  wire  _csr_io_htval_T_3 = ~reset; // @[RocketCore.scala 735:11]
  wire [2:0] _csr_io_rw_cmd_T = wb_reg_valid ? 3'h0 : 3'h4; // @[CSR.scala 168:15]
  wire [2:0] _csr_io_rw_cmd_T_1 = ~_csr_io_rw_cmd_T; // @[CSR.scala 168:11]
  wire [31:0] _T_140 = 32'h1 << ll_waddr; // @[RocketCore.scala 1054:62]
  wire [31:0] _T_141 = ll_wen ? _T_140 : 32'h0; // @[RocketCore.scala 1054:49]
  wire [31:0] _T_142 = ~_T_141; // @[RocketCore.scala 1046:64]
  wire [31:0] _T_143 = r & _T_142; // @[RocketCore.scala 1046:62]
  wire  _T_145 = wb_set_sboard & wb_wen; // @[RocketCore.scala 775:28]
  wire [31:0] _T_146 = 32'h1 << wb_waddr; // @[RocketCore.scala 1054:62]
  wire [31:0] _T_147 = _T_145 ? _T_146 : 32'h0; // @[RocketCore.scala 1054:49]
  wire [31:0] _T_148 = _T_143 | _T_147; // @[RocketCore.scala 1045:60]
  wire  _T_149 = ll_wen | _T_145; // @[RocketCore.scala 1057:17]
  wire [31:0] _io_imem_req_bits_pc_T_1 = replay_wb ? wb_reg_pc : mem_npc; // @[RocketCore.scala 835:8]
  wire  _io_imem_progress_T = ~replay_wb_common; // @[RocketCore.scala 842:47]
  wire [5:0] ex_dcache_tag = {ex_waddr,ex_ctrl_fp}; // @[Cat.scala 31:58]
  wire  unpause = csr_io_time[4:0] == 5'h0 | csr_io_inhibit_cycle | take_pc_mem_wb; // @[RocketCore.scala 910:116]
  wire  coreMonitorBundle_valid = csr_io_trace_0_valid & ~csr_io_trace_0_exception; // @[RocketCore.scala 938:52]
  wire [31:0] coreMonitorBundle_pc = csr_io_trace_0_iaddr; // @[RocketCore.scala 939:48]
  wire  coreMonitorBundle_wrenx = wb_wen & ~wb_set_sboard; // @[RocketCore.scala 940:37]
  reg [31:0] coreMonitorBundle_rd0val_x23; // @[RocketCore.scala 945:43]
  reg [31:0] coreMonitorBundle_rd0val_REG; // @[RocketCore.scala 945:34]
  reg [31:0] coreMonitorBundle_rd1val_x29; // @[RocketCore.scala 947:43]
  reg [31:0] coreMonitorBundle_rd1val_REG; // @[RocketCore.scala 947:34]
  wire [4:0] _T_151 = wb_ctrl_wxd | wb_ctrl_wfd ? wb_waddr : 5'h0; // @[RocketCore.scala 983:13]
  wire [31:0] _T_152 = coreMonitorBundle_wrenx ? rf_wdata : 32'h0; // @[RocketCore.scala 984:13]
  wire  _T_153 = wb_ctrl_rxs1 | wb_ctrl_rfs1; // @[RocketCore.scala 986:27]
  wire [4:0] _T_154 = wb_ctrl_rxs1 | wb_ctrl_rfs1 ? wb_reg_inst[19:15] : 5'h0; // @[RocketCore.scala 986:13]
  wire [31:0] _T_156 = _T_153 ? coreMonitorBundle_rd0val_REG : 32'h0; // @[RocketCore.scala 987:13]
  wire  _T_157 = wb_ctrl_rxs2 | wb_ctrl_rfs2; // @[RocketCore.scala 988:27]
  wire [4:0] _T_158 = wb_ctrl_rxs2 | wb_ctrl_rfs2 ? wb_reg_inst[24:20] : 5'h0; // @[RocketCore.scala 988:13]
  wire [31:0] _T_160 = _T_157 ? coreMonitorBundle_rd1val_REG : 32'h0; // @[RocketCore.scala 989:13]
  wire [31:0] coreMonitorBundle_inst = csr_io_trace_0_insn; // @[RocketCore.scala 932:31 948:26]
  IBuf ibuf ( // @[RocketCore.scala 264:20]
    .clock(ibuf_clock),
    .reset(ibuf_reset),
    .io_imem_ready(ibuf_io_imem_ready),
    .io_imem_valid(ibuf_io_imem_valid),
    .io_imem_bits_pc(ibuf_io_imem_bits_pc),
    .io_imem_bits_data(ibuf_io_imem_bits_data),
    .io_imem_bits_xcpt_ae_inst(ibuf_io_imem_bits_xcpt_ae_inst),
    .io_imem_bits_replay(ibuf_io_imem_bits_replay),
    .io_kill(ibuf_io_kill),
    .io_pc(ibuf_io_pc),
    .io_inst_0_ready(ibuf_io_inst_0_ready),
    .io_inst_0_valid(ibuf_io_inst_0_valid),
    .io_inst_0_bits_xcpt0_ae_inst(ibuf_io_inst_0_bits_xcpt0_ae_inst),
    .io_inst_0_bits_xcpt1_pf_inst(ibuf_io_inst_0_bits_xcpt1_pf_inst),
    .io_inst_0_bits_xcpt1_gf_inst(ibuf_io_inst_0_bits_xcpt1_gf_inst),
    .io_inst_0_bits_xcpt1_ae_inst(ibuf_io_inst_0_bits_xcpt1_ae_inst),
    .io_inst_0_bits_replay(ibuf_io_inst_0_bits_replay),
    .io_inst_0_bits_rvc(ibuf_io_inst_0_bits_rvc),
    .io_inst_0_bits_inst_bits(ibuf_io_inst_0_bits_inst_bits),
    .io_inst_0_bits_inst_rd(ibuf_io_inst_0_bits_inst_rd),
    .io_inst_0_bits_inst_rs1(ibuf_io_inst_0_bits_inst_rs1),
    .io_inst_0_bits_inst_rs2(ibuf_io_inst_0_bits_inst_rs2),
    .io_inst_0_bits_raw(ibuf_io_inst_0_bits_raw)
  );
  CSRFile csr ( // @[RocketCore.scala 293:19]
    .clock(csr_clock),
    .reset(csr_reset),
    .io_ungated_clock(csr_io_ungated_clock),
    .io_interrupts_debug(csr_io_interrupts_debug),
    .io_interrupts_mtip(csr_io_interrupts_mtip),
    .io_interrupts_msip(csr_io_interrupts_msip),
    .io_interrupts_meip(csr_io_interrupts_meip),
    .io_hartid(csr_io_hartid),
    .io_rw_addr(csr_io_rw_addr),
    .io_rw_cmd(csr_io_rw_cmd),
    .io_rw_rdata(csr_io_rw_rdata),
    .io_rw_wdata(csr_io_rw_wdata),
    .io_decode_0_inst(csr_io_decode_0_inst),
    .io_decode_0_fp_illegal(csr_io_decode_0_fp_illegal),
    .io_decode_0_fp_csr(csr_io_decode_0_fp_csr),
    .io_decode_0_rocc_illegal(csr_io_decode_0_rocc_illegal),
    .io_decode_0_read_illegal(csr_io_decode_0_read_illegal),
    .io_decode_0_write_illegal(csr_io_decode_0_write_illegal),
    .io_decode_0_write_flush(csr_io_decode_0_write_flush),
    .io_decode_0_system_illegal(csr_io_decode_0_system_illegal),
    .io_csr_stall(csr_io_csr_stall),
    .io_eret(csr_io_eret),
    .io_singleStep(csr_io_singleStep),
    .io_status_debug(csr_io_status_debug),
    .io_status_cease(csr_io_status_cease),
    .io_status_wfi(csr_io_status_wfi),
    .io_status_isa(csr_io_status_isa),
    .io_status_dprv(csr_io_status_dprv),
    .io_status_dv(csr_io_status_dv),
    .io_status_prv(csr_io_status_prv),
    .io_status_v(csr_io_status_v),
    .io_status_sd(csr_io_status_sd),
    .io_status_zero2(csr_io_status_zero2),
    .io_status_mpv(csr_io_status_mpv),
    .io_status_gva(csr_io_status_gva),
    .io_status_mbe(csr_io_status_mbe),
    .io_status_sbe(csr_io_status_sbe),
    .io_status_sxl(csr_io_status_sxl),
    .io_status_uxl(csr_io_status_uxl),
    .io_status_sd_rv32(csr_io_status_sd_rv32),
    .io_status_zero1(csr_io_status_zero1),
    .io_status_tsr(csr_io_status_tsr),
    .io_status_tw(csr_io_status_tw),
    .io_status_tvm(csr_io_status_tvm),
    .io_status_mxr(csr_io_status_mxr),
    .io_status_sum(csr_io_status_sum),
    .io_status_mprv(csr_io_status_mprv),
    .io_status_xs(csr_io_status_xs),
    .io_status_fs(csr_io_status_fs),
    .io_status_mpp(csr_io_status_mpp),
    .io_status_vs(csr_io_status_vs),
    .io_status_spp(csr_io_status_spp),
    .io_status_mpie(csr_io_status_mpie),
    .io_status_ube(csr_io_status_ube),
    .io_status_spie(csr_io_status_spie),
    .io_status_upie(csr_io_status_upie),
    .io_status_mie(csr_io_status_mie),
    .io_status_hie(csr_io_status_hie),
    .io_status_sie(csr_io_status_sie),
    .io_status_uie(csr_io_status_uie),
    .io_evec(csr_io_evec),
    .io_exception(csr_io_exception),
    .io_retire(csr_io_retire),
    .io_cause(csr_io_cause),
    .io_pc(csr_io_pc),
    .io_tval(csr_io_tval),
    .io_gva(csr_io_gva),
    .io_time(csr_io_time),
    .io_interrupt(csr_io_interrupt),
    .io_interrupt_cause(csr_io_interrupt_cause),
    .io_bp_0_control_action(csr_io_bp_0_control_action),
    .io_bp_0_control_tmatch(csr_io_bp_0_control_tmatch),
    .io_bp_0_control_x(csr_io_bp_0_control_x),
    .io_bp_0_control_w(csr_io_bp_0_control_w),
    .io_bp_0_control_r(csr_io_bp_0_control_r),
    .io_bp_0_address(csr_io_bp_0_address),
    .io_pmp_0_cfg_l(csr_io_pmp_0_cfg_l),
    .io_pmp_0_cfg_a(csr_io_pmp_0_cfg_a),
    .io_pmp_0_cfg_x(csr_io_pmp_0_cfg_x),
    .io_pmp_0_cfg_w(csr_io_pmp_0_cfg_w),
    .io_pmp_0_cfg_r(csr_io_pmp_0_cfg_r),
    .io_pmp_0_addr(csr_io_pmp_0_addr),
    .io_pmp_0_mask(csr_io_pmp_0_mask),
    .io_pmp_1_cfg_l(csr_io_pmp_1_cfg_l),
    .io_pmp_1_cfg_a(csr_io_pmp_1_cfg_a),
    .io_pmp_1_cfg_x(csr_io_pmp_1_cfg_x),
    .io_pmp_1_cfg_w(csr_io_pmp_1_cfg_w),
    .io_pmp_1_cfg_r(csr_io_pmp_1_cfg_r),
    .io_pmp_1_addr(csr_io_pmp_1_addr),
    .io_pmp_1_mask(csr_io_pmp_1_mask),
    .io_pmp_2_cfg_l(csr_io_pmp_2_cfg_l),
    .io_pmp_2_cfg_a(csr_io_pmp_2_cfg_a),
    .io_pmp_2_cfg_x(csr_io_pmp_2_cfg_x),
    .io_pmp_2_cfg_w(csr_io_pmp_2_cfg_w),
    .io_pmp_2_cfg_r(csr_io_pmp_2_cfg_r),
    .io_pmp_2_addr(csr_io_pmp_2_addr),
    .io_pmp_2_mask(csr_io_pmp_2_mask),
    .io_pmp_3_cfg_l(csr_io_pmp_3_cfg_l),
    .io_pmp_3_cfg_a(csr_io_pmp_3_cfg_a),
    .io_pmp_3_cfg_x(csr_io_pmp_3_cfg_x),
    .io_pmp_3_cfg_w(csr_io_pmp_3_cfg_w),
    .io_pmp_3_cfg_r(csr_io_pmp_3_cfg_r),
    .io_pmp_3_addr(csr_io_pmp_3_addr),
    .io_pmp_3_mask(csr_io_pmp_3_mask),
    .io_pmp_4_cfg_l(csr_io_pmp_4_cfg_l),
    .io_pmp_4_cfg_a(csr_io_pmp_4_cfg_a),
    .io_pmp_4_cfg_x(csr_io_pmp_4_cfg_x),
    .io_pmp_4_cfg_w(csr_io_pmp_4_cfg_w),
    .io_pmp_4_cfg_r(csr_io_pmp_4_cfg_r),
    .io_pmp_4_addr(csr_io_pmp_4_addr),
    .io_pmp_4_mask(csr_io_pmp_4_mask),
    .io_pmp_5_cfg_l(csr_io_pmp_5_cfg_l),
    .io_pmp_5_cfg_a(csr_io_pmp_5_cfg_a),
    .io_pmp_5_cfg_x(csr_io_pmp_5_cfg_x),
    .io_pmp_5_cfg_w(csr_io_pmp_5_cfg_w),
    .io_pmp_5_cfg_r(csr_io_pmp_5_cfg_r),
    .io_pmp_5_addr(csr_io_pmp_5_addr),
    .io_pmp_5_mask(csr_io_pmp_5_mask),
    .io_pmp_6_cfg_l(csr_io_pmp_6_cfg_l),
    .io_pmp_6_cfg_a(csr_io_pmp_6_cfg_a),
    .io_pmp_6_cfg_x(csr_io_pmp_6_cfg_x),
    .io_pmp_6_cfg_w(csr_io_pmp_6_cfg_w),
    .io_pmp_6_cfg_r(csr_io_pmp_6_cfg_r),
    .io_pmp_6_addr(csr_io_pmp_6_addr),
    .io_pmp_6_mask(csr_io_pmp_6_mask),
    .io_pmp_7_cfg_l(csr_io_pmp_7_cfg_l),
    .io_pmp_7_cfg_a(csr_io_pmp_7_cfg_a),
    .io_pmp_7_cfg_x(csr_io_pmp_7_cfg_x),
    .io_pmp_7_cfg_w(csr_io_pmp_7_cfg_w),
    .io_pmp_7_cfg_r(csr_io_pmp_7_cfg_r),
    .io_pmp_7_addr(csr_io_pmp_7_addr),
    .io_pmp_7_mask(csr_io_pmp_7_mask),
    .io_inhibit_cycle(csr_io_inhibit_cycle),
    .io_inst_0(csr_io_inst_0),
    .io_trace_0_valid(csr_io_trace_0_valid),
    .io_trace_0_iaddr(csr_io_trace_0_iaddr),
    .io_trace_0_insn(csr_io_trace_0_insn),
    .io_trace_0_exception(csr_io_trace_0_exception),
    .io_customCSRs_0_value(csr_io_customCSRs_0_value)
  );
  
  BreakpointUnit bpu ( // @[RocketCore.scala 336:19]
    .io_status_debug(bpu_io_status_debug),
    .io_bp_0_control_action(bpu_io_bp_0_control_action),
    .io_bp_0_control_tmatch(bpu_io_bp_0_control_tmatch),
    .io_bp_0_control_x(bpu_io_bp_0_control_x),
    .io_bp_0_control_w(bpu_io_bp_0_control_w),
    .io_bp_0_control_r(bpu_io_bp_0_control_r),
    .io_bp_0_address(bpu_io_bp_0_address),
    .io_pc(bpu_io_pc),
    .io_ea(bpu_io_ea),
    .io_xcpt_if(bpu_io_xcpt_if),
    .io_xcpt_ld(bpu_io_xcpt_ld),
    .io_xcpt_st(bpu_io_xcpt_st),
    .io_debug_if(bpu_io_debug_if),
    .io_debug_ld(bpu_io_debug_ld),
    .io_debug_st(bpu_io_debug_st)
  );
  ALU alu ( // @[RocketCore.scala 401:19]
    .io_fn(alu_io_fn),
    .io_in2(alu_io_in2),
    .io_in1(alu_io_in1),
    .io_out(alu_io_out),
    .io_adder_out(alu_io_adder_out),
    .io_cmp_out(alu_io_cmp_out)
  );
  MulDiv div ( // @[RocketCore.scala 425:19]
    .clock(div_clock),
    .reset(div_reset),
    .io_req_ready(div_io_req_ready),
    .io_req_valid(div_io_req_valid),
    .io_req_bits_fn(div_io_req_bits_fn),
    .io_req_bits_in1(div_io_req_bits_in1),
    .io_req_bits_in2(div_io_req_bits_in2),
    .io_req_bits_tag(div_io_req_bits_tag),
    .io_kill(div_io_kill),
    .io_resp_ready(div_io_resp_ready),
    .io_resp_valid(div_io_resp_valid),
    .io_resp_bits_data(div_io_resp_bits_data),
    .io_resp_bits_tag(div_io_resp_bits_tag)
  );
  PlusArgTimeout PlusArgTimeout ( // @[PlusArg.scala 89:11]
    .clock(PlusArgTimeout_clock),
    .reset(PlusArgTimeout_reset),
    .io_count(PlusArgTimeout_io_count)
  );
  assign rf_id_rs_MPORT_en = 1'h1;
  assign rf_id_rs_MPORT_addr = ~id_raddr1;
  `ifndef RANDOMIZE_GARBAGE_ASSIGN
  assign rf_id_rs_MPORT_data = rf[rf_id_rs_MPORT_addr]; // @[RocketCore.scala 1064:15]
  `else
  assign rf_id_rs_MPORT_data = rf_id_rs_MPORT_addr >= 5'h1f ? _RAND_1[31:0] : rf[rf_id_rs_MPORT_addr]; // @[RocketCore.scala 1064:15]
  `endif // RANDOMIZE_GARBAGE_ASSIGN
  assign rf_id_rs_MPORT_1_en = 1'h1;
  assign rf_id_rs_MPORT_1_addr = ~id_raddr2;
  `ifndef RANDOMIZE_GARBAGE_ASSIGN
  assign rf_id_rs_MPORT_1_data = rf[rf_id_rs_MPORT_1_addr]; // @[RocketCore.scala 1064:15]
  `else
  assign rf_id_rs_MPORT_1_data = rf_id_rs_MPORT_1_addr >= 5'h1f ? _RAND_2[31:0] : rf[rf_id_rs_MPORT_1_addr]; // @[RocketCore.scala 1064:15]
  `endif // RANDOMIZE_GARBAGE_ASSIGN
  assign rf_MPORT_data = _rf_wdata_T ? io_dmem_resp_bits_data : _rf_wdata_T_5;
  assign rf_MPORT_addr = ~rf_waddr;
  assign rf_MPORT_mask = 1'h1;
  assign rf_MPORT_en = rf_wen & _T_129;
  assign io_imem_might_request = imem_might_request_reg; // @[RocketCore.scala 838:25]
  assign io_imem_req_valid = take_pc_wb | take_pc_mem; // @[RocketCore.scala 260:35]
  assign io_imem_req_bits_pc = wb_xcpt | csr_io_eret ? csr_io_evec : _io_imem_req_bits_pc_T_1; // @[RocketCore.scala 834:8]
  assign io_imem_req_bits_speculative = ~take_pc_wb; // @[RocketCore.scala 832:35]
  assign io_imem_resp_ready = ibuf_io_imem_ready; // @[RocketCore.scala 268:16]
  assign io_imem_btb_update_valid = mem_reg_valid & _wb_reg_replay_T & mem_wrong_npc & (~mem_cfi | mem_cfi_taken); // @[RocketCore.scala 854:77]
  assign io_imem_bht_update_valid = mem_reg_valid & _wb_reg_replay_T; // @[RocketCore.scala 866:45]
  assign io_imem_flush_icache = wb_reg_valid & wb_ctrl_fence_i & ~io_dmem_s2_nack; // @[RocketCore.scala 837:59]
  assign io_dmem_req_valid = ex_reg_valid & ex_ctrl_mem; // @[RocketCore.scala 884:41]
  assign io_dmem_req_bits_addr = alu_io_adder_out; // @[RocketCore.scala 892:25]
  assign io_dmem_req_bits_tag = {{1'd0}, ex_dcache_tag}; // @[RocketCore.scala 887:25]
  assign io_dmem_req_bits_cmd = ex_ctrl_mem_cmd; // @[RocketCore.scala 888:25]
  assign io_dmem_req_bits_size = ex_reg_mem_size; // @[RocketCore.scala 889:25]
  assign io_dmem_req_bits_signed = ~ex_reg_inst[14]; // @[RocketCore.scala 890:30]
  assign io_dmem_req_bits_dv = 1'h0; // @[RocketCore.scala 895:37]
  assign io_dmem_s1_kill = killm_common | mem_ldst_xcpt; // @[RocketCore.scala 897:35]
  assign io_dmem_s1_data_data = mem_reg_rs2; // @[RocketCore.scala 896:24]
  assign io_ptw_status_debug = csr_io_status_debug; // @[RocketCore.scala 746:17]
  assign io_ptw_pmp_0_cfg_l = csr_io_pmp_0_cfg_l; // @[RocketCore.scala 749:14]
  assign io_ptw_pmp_0_cfg_a = csr_io_pmp_0_cfg_a; // @[RocketCore.scala 749:14]
  assign io_ptw_pmp_0_cfg_x = csr_io_pmp_0_cfg_x; // @[RocketCore.scala 749:14]
  assign io_ptw_pmp_0_cfg_w = csr_io_pmp_0_cfg_w; // @[RocketCore.scala 749:14]
  assign io_ptw_pmp_0_cfg_r = csr_io_pmp_0_cfg_r; // @[RocketCore.scala 749:14]
  assign io_ptw_pmp_0_addr = csr_io_pmp_0_addr; // @[RocketCore.scala 749:14]
  assign io_ptw_pmp_0_mask = csr_io_pmp_0_mask; // @[RocketCore.scala 749:14]
  assign io_ptw_pmp_1_cfg_l = csr_io_pmp_1_cfg_l; // @[RocketCore.scala 749:14]
  assign io_ptw_pmp_1_cfg_a = csr_io_pmp_1_cfg_a; // @[RocketCore.scala 749:14]
  assign io_ptw_pmp_1_cfg_x = csr_io_pmp_1_cfg_x; // @[RocketCore.scala 749:14]
  assign io_ptw_pmp_1_cfg_w = csr_io_pmp_1_cfg_w; // @[RocketCore.scala 749:14]
  assign io_ptw_pmp_1_cfg_r = csr_io_pmp_1_cfg_r; // @[RocketCore.scala 749:14]
  assign io_ptw_pmp_1_addr = csr_io_pmp_1_addr; // @[RocketCore.scala 749:14]
  assign io_ptw_pmp_1_mask = csr_io_pmp_1_mask; // @[RocketCore.scala 749:14]
  assign io_ptw_pmp_2_cfg_l = csr_io_pmp_2_cfg_l; // @[RocketCore.scala 749:14]
  assign io_ptw_pmp_2_cfg_a = csr_io_pmp_2_cfg_a; // @[RocketCore.scala 749:14]
  assign io_ptw_pmp_2_cfg_x = csr_io_pmp_2_cfg_x; // @[RocketCore.scala 749:14]
  assign io_ptw_pmp_2_cfg_w = csr_io_pmp_2_cfg_w; // @[RocketCore.scala 749:14]
  assign io_ptw_pmp_2_cfg_r = csr_io_pmp_2_cfg_r; // @[RocketCore.scala 749:14]
  assign io_ptw_pmp_2_addr = csr_io_pmp_2_addr; // @[RocketCore.scala 749:14]
  assign io_ptw_pmp_2_mask = csr_io_pmp_2_mask; // @[RocketCore.scala 749:14]
  assign io_ptw_pmp_3_cfg_l = csr_io_pmp_3_cfg_l; // @[RocketCore.scala 749:14]
  assign io_ptw_pmp_3_cfg_a = csr_io_pmp_3_cfg_a; // @[RocketCore.scala 749:14]
  assign io_ptw_pmp_3_cfg_x = csr_io_pmp_3_cfg_x; // @[RocketCore.scala 749:14]
  assign io_ptw_pmp_3_cfg_w = csr_io_pmp_3_cfg_w; // @[RocketCore.scala 749:14]
  assign io_ptw_pmp_3_cfg_r = csr_io_pmp_3_cfg_r; // @[RocketCore.scala 749:14]
  assign io_ptw_pmp_3_addr = csr_io_pmp_3_addr; // @[RocketCore.scala 749:14]
  assign io_ptw_pmp_3_mask = csr_io_pmp_3_mask; // @[RocketCore.scala 749:14]
  assign io_ptw_pmp_4_cfg_l = csr_io_pmp_4_cfg_l; // @[RocketCore.scala 749:14]
  assign io_ptw_pmp_4_cfg_a = csr_io_pmp_4_cfg_a; // @[RocketCore.scala 749:14]
  assign io_ptw_pmp_4_cfg_x = csr_io_pmp_4_cfg_x; // @[RocketCore.scala 749:14]
  assign io_ptw_pmp_4_cfg_w = csr_io_pmp_4_cfg_w; // @[RocketCore.scala 749:14]
  assign io_ptw_pmp_4_cfg_r = csr_io_pmp_4_cfg_r; // @[RocketCore.scala 749:14]
  assign io_ptw_pmp_4_addr = csr_io_pmp_4_addr; // @[RocketCore.scala 749:14]
  assign io_ptw_pmp_4_mask = csr_io_pmp_4_mask; // @[RocketCore.scala 749:14]
  assign io_ptw_pmp_5_cfg_l = csr_io_pmp_5_cfg_l; // @[RocketCore.scala 749:14]
  assign io_ptw_pmp_5_cfg_a = csr_io_pmp_5_cfg_a; // @[RocketCore.scala 749:14]
  assign io_ptw_pmp_5_cfg_x = csr_io_pmp_5_cfg_x; // @[RocketCore.scala 749:14]
  assign io_ptw_pmp_5_cfg_w = csr_io_pmp_5_cfg_w; // @[RocketCore.scala 749:14]
  assign io_ptw_pmp_5_cfg_r = csr_io_pmp_5_cfg_r; // @[RocketCore.scala 749:14]
  assign io_ptw_pmp_5_addr = csr_io_pmp_5_addr; // @[RocketCore.scala 749:14]
  assign io_ptw_pmp_5_mask = csr_io_pmp_5_mask; // @[RocketCore.scala 749:14]
  assign io_ptw_pmp_6_cfg_l = csr_io_pmp_6_cfg_l; // @[RocketCore.scala 749:14]
  assign io_ptw_pmp_6_cfg_a = csr_io_pmp_6_cfg_a; // @[RocketCore.scala 749:14]
  assign io_ptw_pmp_6_cfg_x = csr_io_pmp_6_cfg_x; // @[RocketCore.scala 749:14]
  assign io_ptw_pmp_6_cfg_w = csr_io_pmp_6_cfg_w; // @[RocketCore.scala 749:14]
  assign io_ptw_pmp_6_cfg_r = csr_io_pmp_6_cfg_r; // @[RocketCore.scala 749:14]
  assign io_ptw_pmp_6_addr = csr_io_pmp_6_addr; // @[RocketCore.scala 749:14]
  assign io_ptw_pmp_6_mask = csr_io_pmp_6_mask; // @[RocketCore.scala 749:14]
  assign io_ptw_pmp_7_cfg_l = csr_io_pmp_7_cfg_l; // @[RocketCore.scala 749:14]
  assign io_ptw_pmp_7_cfg_a = csr_io_pmp_7_cfg_a; // @[RocketCore.scala 749:14]
  assign io_ptw_pmp_7_cfg_x = csr_io_pmp_7_cfg_x; // @[RocketCore.scala 749:14]
  assign io_ptw_pmp_7_cfg_w = csr_io_pmp_7_cfg_w; // @[RocketCore.scala 749:14]
  assign io_ptw_pmp_7_cfg_r = csr_io_pmp_7_cfg_r; // @[RocketCore.scala 749:14]
  assign io_ptw_pmp_7_addr = csr_io_pmp_7_addr; // @[RocketCore.scala 749:14]
  assign io_ptw_pmp_7_mask = csr_io_pmp_7_mask; // @[RocketCore.scala 749:14]
  assign io_ptw_customCSRs_csrs_0_value = csr_io_customCSRs_0_value; // @[RocketCore.scala 745:79]
  assign io_rocc_cmd_valid = replay_wb_rocc & _io_imem_progress_T; // @[RocketCore.scala 902:53]
  assign io_wfi = csr_io_status_wfi; // @[RocketCore.scala 913:10]
  assign ibuf_clock = clock;
  assign ibuf_reset = reset;
  assign ibuf_io_imem_valid = io_imem_resp_valid; // @[RocketCore.scala 268:16]
  assign ibuf_io_imem_bits_pc = io_imem_resp_bits_pc; // @[RocketCore.scala 268:16]
  assign ibuf_io_imem_bits_data = io_imem_resp_bits_data; // @[RocketCore.scala 268:16]
  assign ibuf_io_imem_bits_xcpt_ae_inst = io_imem_resp_bits_xcpt_ae_inst; // @[RocketCore.scala 268:16]
  assign ibuf_io_imem_bits_replay = io_imem_resp_bits_replay; // @[RocketCore.scala 268:16]
  assign ibuf_io_kill = take_pc_wb | take_pc_mem; // @[RocketCore.scala 260:35]
  assign ibuf_io_inst_0_ready = ~ctrl_stalld; // @[RocketCore.scala 852:28]
  assign csr_clock = clock;
  assign csr_reset = reset;
  assign csr_io_ungated_clock = clock; // @[RocketCore.scala 711:24]
  assign csr_io_interrupts_debug = io_interrupts_debug; // @[RocketCore.scala 717:21]
  assign csr_io_interrupts_mtip = io_interrupts_mtip; // @[RocketCore.scala 717:21]
  assign csr_io_interrupts_msip = io_interrupts_msip; // @[RocketCore.scala 717:21]
  assign csr_io_interrupts_meip = io_interrupts_meip; // @[RocketCore.scala 717:21]
  assign csr_io_hartid = io_hartid; // @[RocketCore.scala 718:17]
  assign csr_io_rw_addr = wb_reg_inst[31:20]; // @[RocketCore.scala 750:32]
  assign csr_io_rw_cmd = wb_ctrl_csr & _csr_io_rw_cmd_T_1; // @[CSR.scala 168:9]
  assign csr_io_rw_wdata = wb_reg_wdata; // @[RocketCore.scala 752:19]
  assign csr_io_decode_0_inst = ibuf_io_inst_0_bits_inst_bits; // @[RocketCore.scala 712:25]
  assign csr_io_exception = wb_reg_xcpt | _T_91 | _T_93 | _T_99 | _T_101 | _T_103 | _T_105; // @[RocketCore.scala 1024:26]
  assign csr_io_retire = wb_reg_valid & ~replay_wb & ~wb_xcpt; // @[RocketCore.scala 699:45]
  assign csr_io_cause = wb_reg_xcpt ? wb_reg_cause : {{27'd0}, _T_119}; // @[Mux.scala 47:70]
  assign csr_io_pc = wb_reg_pc; // @[RocketCore.scala 724:13]
  assign csr_io_tval = tval_valid ? wb_reg_wdata : 32'h0; // @[RocketCore.scala 731:21]
  assign csr_io_gva = wb_xcpt & (tval_dmem_addr & wb_reg_hls_or_dv); // @[RocketCore.scala 730:25]
  assign csr_io_inst_0 = {_csr_io_inst_0_T_3,wb_reg_raw_inst[15:0]}; // @[Cat.scala 31:58]
  assign bpu_io_status_debug = csr_io_status_debug; // @[RocketCore.scala 337:17]
  assign bpu_io_bp_0_control_action = csr_io_bp_0_control_action; // @[RocketCore.scala 338:13]
  assign bpu_io_bp_0_control_tmatch = csr_io_bp_0_control_tmatch; // @[RocketCore.scala 338:13]
  assign bpu_io_bp_0_control_x = csr_io_bp_0_control_x; // @[RocketCore.scala 338:13]
  assign bpu_io_bp_0_control_w = csr_io_bp_0_control_w; // @[RocketCore.scala 338:13]
  assign bpu_io_bp_0_control_r = csr_io_bp_0_control_r; // @[RocketCore.scala 338:13]
  assign bpu_io_bp_0_address = csr_io_bp_0_address; // @[RocketCore.scala 338:13]
  assign bpu_io_pc = ibuf_io_pc; // @[RocketCore.scala 339:13]
  assign bpu_io_ea = mem_reg_wdata; // @[RocketCore.scala 340:13]
  assign alu_io_fn = ex_ctrl_alu_fn; // @[RocketCore.scala 403:13]
  assign alu_io_in2 = 2'h1 == ex_ctrl_sel_alu2 ? $signed({{28{_ex_op2_T_1[3]}},_ex_op2_T_1}) : $signed(_ex_op2_T_5); // @[RocketCore.scala 404:24]
  assign alu_io_in1 = 2'h2 == ex_ctrl_sel_alu1 ? $signed(ex_reg_pc) : $signed(_ex_op1_T_3); // @[RocketCore.scala 405:24]
  assign div_clock = clock;
  assign div_reset = reset;
  assign div_io_req_valid = ex_reg_valid & ex_ctrl_div; // @[RocketCore.scala 426:36]
  assign div_io_req_bits_fn = ex_ctrl_alu_fn; // @[RocketCore.scala 428:22]
  assign div_io_req_bits_in1 = ex_reg_rs_bypass_0 ? _ex_rs_T_5 : _ex_rs_T_6; // @[RocketCore.scala 391:14]
  assign div_io_req_bits_in2 = ex_reg_rs_bypass_1 ? _ex_rs_T_12 : _ex_rs_T_13; // @[RocketCore.scala 391:14]
  assign div_io_req_bits_tag = ex_reg_inst[11:7]; // @[RocketCore.scala 375:29]
  assign div_io_kill = killm_common & div_io_kill_REG; // @[RocketCore.scala 609:31]
  assign div_io_resp_ready = dmem_resp_replay & dmem_resp_xpu ? 1'h0 : _ctrl_stalld_T_17; // @[RocketCore.scala 678:21 691:44 692:23]
  assign PlusArgTimeout_clock = clock;
  assign PlusArgTimeout_reset = reset;
  assign PlusArgTimeout_io_count = csr_io_time; // @[PlusArg.scala 89:82]
  always @(posedge clock) begin
    if (rf_MPORT_en & rf_MPORT_mask) begin
      rf[rf_MPORT_addr] <= rf_MPORT_data; // @[RocketCore.scala 1064:15]
    end
    if (unpause) begin // @[RocketCore.scala 911:18]
      id_reg_pause <= 1'h0; // @[RocketCore.scala 911:33]
    end else if (_ex_reg_valid_T) begin // @[RocketCore.scala 444:22]
      id_reg_pause <= _GEN_1;
    end
    imem_might_request_reg <= ex_pc_valid | mem_pc_valid | io_ptw_customCSRs_csrs_0_value[1]; // @[RocketCore.scala 839:59]
    if (_ex_reg_valid_T) begin // @[RocketCore.scala 444:22]
      ex_ctrl_fp <= id_ctrl_decoder_1; // @[RocketCore.scala 445:13]
    end
    if (_ex_reg_valid_T) begin // @[RocketCore.scala 444:22]
      ex_ctrl_rocc <= id_ctrl_decoder_2; // @[RocketCore.scala 445:13]
    end
    if (_ex_reg_valid_T) begin // @[RocketCore.scala 444:22]
      ex_ctrl_branch <= id_ctrl_decoder_3; // @[RocketCore.scala 445:13]
    end
    if (_ex_reg_valid_T) begin // @[RocketCore.scala 444:22]
      ex_ctrl_jal <= id_ctrl_decoder_4; // @[RocketCore.scala 445:13]
    end
    if (_ex_reg_valid_T) begin // @[RocketCore.scala 444:22]
      ex_ctrl_jalr <= id_ctrl_decoder_5; // @[RocketCore.scala 445:13]
    end
    if (_ex_reg_valid_T) begin // @[RocketCore.scala 444:22]
      ex_ctrl_rxs2 <= id_ctrl_decoder_6; // @[RocketCore.scala 445:13]
    end
    if (_ex_reg_valid_T) begin // @[RocketCore.scala 444:22]
      ex_ctrl_rxs1 <= id_ctrl_decoder_7; // @[RocketCore.scala 445:13]
    end
    if (_ex_reg_valid_T) begin // @[RocketCore.scala 444:22]
      if (id_xcpt) begin // @[RocketCore.scala 452:20]
        if (bpu_io_xcpt_if | |_T_37) begin // @[RocketCore.scala 462:52]
          ex_ctrl_sel_alu2 <= 2'h0; // @[RocketCore.scala 464:26]
        end else if (|_T_35) begin // @[RocketCore.scala 457:34]
          ex_ctrl_sel_alu2 <= 2'h1; // @[RocketCore.scala 459:26]
        end else begin
          ex_ctrl_sel_alu2 <= 2'h0; // @[RocketCore.scala 456:24]
        end
      end else begin
        ex_ctrl_sel_alu2 <= id_ctrl_decoder_9; // @[RocketCore.scala 445:13]
      end
    end
    if (_ex_reg_valid_T) begin // @[RocketCore.scala 444:22]
      if (id_xcpt) begin // @[RocketCore.scala 452:20]
        if (bpu_io_xcpt_if | |_T_37) begin // @[RocketCore.scala 462:52]
          ex_ctrl_sel_alu1 <= 2'h2; // @[RocketCore.scala 463:26]
        end else if (|_T_35) begin // @[RocketCore.scala 457:34]
          ex_ctrl_sel_alu1 <= 2'h2; // @[RocketCore.scala 458:26]
        end else begin
          ex_ctrl_sel_alu1 <= 2'h1; // @[RocketCore.scala 455:24]
        end
      end else begin
        ex_ctrl_sel_alu1 <= id_ctrl_decoder_10; // @[RocketCore.scala 445:13]
      end
    end
    if (_ex_reg_valid_T) begin // @[RocketCore.scala 444:22]
      ex_ctrl_sel_imm <= id_ctrl_decoder_11; // @[RocketCore.scala 445:13]
    end
    if (_ex_reg_valid_T) begin // @[RocketCore.scala 444:22]
      if (id_xcpt) begin // @[RocketCore.scala 452:20]
        ex_ctrl_alu_fn <= 4'h0; // @[RocketCore.scala 453:22]
      end else begin
        ex_ctrl_alu_fn <= id_ctrl_decoder_13; // @[RocketCore.scala 445:13]
      end
    end
    if (_ex_reg_valid_T) begin // @[RocketCore.scala 444:22]
      ex_ctrl_mem <= id_ctrl_decoder_14; // @[RocketCore.scala 445:13]
    end
    if (_ex_reg_valid_T) begin // @[RocketCore.scala 444:22]
      ex_ctrl_mem_cmd <= id_ctrl_decoder_15;
    end
    if (_ex_reg_valid_T) begin // @[RocketCore.scala 444:22]
      ex_ctrl_rfs1 <= id_ctrl_decoder_16; // @[RocketCore.scala 445:13]
    end
    if (_ex_reg_valid_T) begin // @[RocketCore.scala 444:22]
      ex_ctrl_rfs2 <= id_ctrl_decoder_17; // @[RocketCore.scala 445:13]
    end
    if (_ex_reg_valid_T) begin // @[RocketCore.scala 444:22]
      ex_ctrl_wfd <= id_ctrl_decoder_19; // @[RocketCore.scala 445:13]
    end
    if (_ex_reg_valid_T) begin // @[RocketCore.scala 444:22]
      ex_ctrl_mul <= id_ctrl_decoder_20; // @[RocketCore.scala 445:13]
    end
    if (_ex_reg_valid_T) begin // @[RocketCore.scala 444:22]
      ex_ctrl_div <= id_ctrl_decoder_21; // @[RocketCore.scala 445:13]
    end
    if (_ex_reg_valid_T) begin // @[RocketCore.scala 444:22]
      ex_ctrl_wxd <= id_ctrl_decoder_22; // @[RocketCore.scala 445:13]
    end
    if (_ex_reg_valid_T) begin // @[RocketCore.scala 444:22]
      if (id_system_insn & id_ctrl_decoder_14) begin // @[RocketCore.scala 297:19]
        ex_ctrl_csr <= 3'h0;
      end else if (id_csr_ren) begin // @[RocketCore.scala 297:61]
        ex_ctrl_csr <= 3'h2;
      end else begin
        ex_ctrl_csr <= id_ctrl_decoder_23;
      end
    end
    if (_ex_reg_valid_T) begin // @[RocketCore.scala 444:22]
      ex_ctrl_fence_i <= id_ctrl_decoder_24; // @[RocketCore.scala 445:13]
    end
    if (!(mem_reg_valid & mem_reg_flush_pipe)) begin // @[RocketCore.scala 552:46]
      if (ex_pc_valid) begin // @[RocketCore.scala 554:28]
        mem_ctrl_fp <= ex_ctrl_fp; // @[RocketCore.scala 555:14]
      end
    end
    if (!(mem_reg_valid & mem_reg_flush_pipe)) begin // @[RocketCore.scala 552:46]
      if (ex_pc_valid) begin // @[RocketCore.scala 554:28]
        mem_ctrl_rocc <= ex_ctrl_rocc; // @[RocketCore.scala 555:14]
      end
    end
    if (!(mem_reg_valid & mem_reg_flush_pipe)) begin // @[RocketCore.scala 552:46]
      if (ex_pc_valid) begin // @[RocketCore.scala 554:28]
        mem_ctrl_branch <= ex_ctrl_branch; // @[RocketCore.scala 555:14]
      end
    end
    if (!(mem_reg_valid & mem_reg_flush_pipe)) begin // @[RocketCore.scala 552:46]
      if (ex_pc_valid) begin // @[RocketCore.scala 554:28]
        mem_ctrl_jal <= ex_ctrl_jal; // @[RocketCore.scala 555:14]
      end
    end
    if (!(mem_reg_valid & mem_reg_flush_pipe)) begin // @[RocketCore.scala 552:46]
      if (ex_pc_valid) begin // @[RocketCore.scala 554:28]
        mem_ctrl_jalr <= ex_ctrl_jalr; // @[RocketCore.scala 555:14]
      end
    end
    if (!(mem_reg_valid & mem_reg_flush_pipe)) begin // @[RocketCore.scala 552:46]
      if (ex_pc_valid) begin // @[RocketCore.scala 554:28]
        mem_ctrl_rxs2 <= ex_ctrl_rxs2; // @[RocketCore.scala 555:14]
      end
    end
    if (!(mem_reg_valid & mem_reg_flush_pipe)) begin // @[RocketCore.scala 552:46]
      if (ex_pc_valid) begin // @[RocketCore.scala 554:28]
        mem_ctrl_rxs1 <= ex_ctrl_rxs1; // @[RocketCore.scala 555:14]
      end
    end
    if (!(mem_reg_valid & mem_reg_flush_pipe)) begin // @[RocketCore.scala 552:46]
      if (ex_pc_valid) begin // @[RocketCore.scala 554:28]
        mem_ctrl_mem <= ex_ctrl_mem; // @[RocketCore.scala 555:14]
      end
    end
    if (!(mem_reg_valid & mem_reg_flush_pipe)) begin // @[RocketCore.scala 552:46]
      if (ex_pc_valid) begin // @[RocketCore.scala 554:28]
        mem_ctrl_rfs1 <= ex_ctrl_rfs1; // @[RocketCore.scala 555:14]
      end
    end
    if (!(mem_reg_valid & mem_reg_flush_pipe)) begin // @[RocketCore.scala 552:46]
      if (ex_pc_valid) begin // @[RocketCore.scala 554:28]
        mem_ctrl_rfs2 <= ex_ctrl_rfs2; // @[RocketCore.scala 555:14]
      end
    end
    if (!(mem_reg_valid & mem_reg_flush_pipe)) begin // @[RocketCore.scala 552:46]
      if (ex_pc_valid) begin // @[RocketCore.scala 554:28]
        mem_ctrl_wfd <= ex_ctrl_wfd; // @[RocketCore.scala 555:14]
      end
    end
    if (!(mem_reg_valid & mem_reg_flush_pipe)) begin // @[RocketCore.scala 552:46]
      if (ex_pc_valid) begin // @[RocketCore.scala 554:28]
        mem_ctrl_mul <= ex_ctrl_mul; // @[RocketCore.scala 555:14]
      end
    end
    if (!(mem_reg_valid & mem_reg_flush_pipe)) begin // @[RocketCore.scala 552:46]
      if (ex_pc_valid) begin // @[RocketCore.scala 554:28]
        mem_ctrl_div <= ex_ctrl_div; // @[RocketCore.scala 555:14]
      end
    end
    if (!(mem_reg_valid & mem_reg_flush_pipe)) begin // @[RocketCore.scala 552:46]
      if (ex_pc_valid) begin // @[RocketCore.scala 554:28]
        mem_ctrl_wxd <= ex_ctrl_wxd; // @[RocketCore.scala 555:14]
      end
    end
    if (!(mem_reg_valid & mem_reg_flush_pipe)) begin // @[RocketCore.scala 552:46]
      if (ex_pc_valid) begin // @[RocketCore.scala 554:28]
        mem_ctrl_csr <= ex_ctrl_csr; // @[RocketCore.scala 555:14]
      end
    end
    if (!(mem_reg_valid & mem_reg_flush_pipe)) begin // @[RocketCore.scala 552:46]
      if (ex_pc_valid) begin // @[RocketCore.scala 554:28]
        mem_ctrl_fence_i <= _GEN_79;
      end
    end
    if (mem_pc_valid) begin // @[RocketCore.scala 617:23]
      wb_ctrl_rocc <= mem_ctrl_rocc; // @[RocketCore.scala 618:13]
    end
    if (mem_pc_valid) begin // @[RocketCore.scala 617:23]
      wb_ctrl_rxs2 <= mem_ctrl_rxs2; // @[RocketCore.scala 618:13]
    end
    if (mem_pc_valid) begin // @[RocketCore.scala 617:23]
      wb_ctrl_rxs1 <= mem_ctrl_rxs1; // @[RocketCore.scala 618:13]
    end
    if (mem_pc_valid) begin // @[RocketCore.scala 617:23]
      wb_ctrl_mem <= mem_ctrl_mem; // @[RocketCore.scala 618:13]
    end
    if (mem_pc_valid) begin // @[RocketCore.scala 617:23]
      wb_ctrl_rfs1 <= mem_ctrl_rfs1; // @[RocketCore.scala 618:13]
    end
    if (mem_pc_valid) begin // @[RocketCore.scala 617:23]
      wb_ctrl_rfs2 <= mem_ctrl_rfs2; // @[RocketCore.scala 618:13]
    end
    if (mem_pc_valid) begin // @[RocketCore.scala 617:23]
      wb_ctrl_wfd <= mem_ctrl_wfd; // @[RocketCore.scala 618:13]
    end
    if (mem_pc_valid) begin // @[RocketCore.scala 617:23]
      wb_ctrl_div <= mem_ctrl_div; // @[RocketCore.scala 618:13]
    end
    if (mem_pc_valid) begin // @[RocketCore.scala 617:23]
      wb_ctrl_wxd <= mem_ctrl_wxd; // @[RocketCore.scala 618:13]
    end
    if (mem_pc_valid) begin // @[RocketCore.scala 617:23]
      wb_ctrl_csr <= mem_ctrl_csr; // @[RocketCore.scala 618:13]
    end
    if (mem_pc_valid) begin // @[RocketCore.scala 617:23]
      wb_ctrl_fence_i <= mem_ctrl_fence_i; // @[RocketCore.scala 618:13]
    end
    ex_reg_xcpt_interrupt <= _ex_reg_replay_T_1 & csr_io_interrupt; // @[RocketCore.scala 442:62]
    ex_reg_valid <= ~ctrl_killd; // @[RocketCore.scala 439:19]
    if (_ex_reg_valid_T) begin // @[RocketCore.scala 444:22]
      if (id_xcpt) begin // @[RocketCore.scala 452:20]
        ex_reg_rvc <= _GEN_5;
      end else begin
        ex_reg_rvc <= ibuf_io_inst_0_bits_rvc; // @[RocketCore.scala 446:16]
      end
    end
    ex_reg_xcpt <= _ex_reg_valid_T & id_xcpt; // @[RocketCore.scala 441:30]
    if (_ex_reg_valid_T) begin // @[RocketCore.scala 444:22]
      ex_reg_flush_pipe <= id_ctrl_decoder_24 | id_csr_flush; // @[RocketCore.scala 467:23]
    end
    if (_ex_reg_valid_T) begin // @[RocketCore.scala 444:22]
      ex_reg_load_use <= id_load_use; // @[RocketCore.scala 468:21]
    end
    if (_ex_reg_valid_T | csr_io_interrupt | ibuf_io_inst_0_bits_replay) begin // @[RocketCore.scala 500:73]
      if (csr_io_interrupt) begin // @[Mux.scala 47:70]
        ex_reg_cause <= csr_io_interrupt_cause;
      end else begin
        ex_reg_cause <= {{27'd0}, _T_18};
      end
    end
    ex_reg_replay <= ~take_pc_mem_wb & ibuf_io_inst_0_valid & ibuf_io_inst_0_bits_replay; // @[RocketCore.scala 440:54]
    if (_ex_reg_valid_T | csr_io_interrupt | ibuf_io_inst_0_bits_replay) begin // @[RocketCore.scala 500:73]
      ex_reg_pc <= ibuf_io_pc; // @[RocketCore.scala 504:15]
    end
    if (_ex_reg_valid_T) begin // @[RocketCore.scala 444:22]
      if (_T_46) begin // @[RocketCore.scala 471:81]
        ex_reg_mem_size <= _ex_reg_mem_size_T_6; // @[RocketCore.scala 472:23]
      end else begin
        ex_reg_mem_size <= ibuf_io_inst_0_bits_inst_bits[13:12]; // @[RocketCore.scala 470:21]
      end
    end
    if (_ex_reg_valid_T | csr_io_interrupt | ibuf_io_inst_0_bits_replay) begin // @[RocketCore.scala 500:73]
      ex_reg_inst <= ibuf_io_inst_0_bits_inst_bits; // @[RocketCore.scala 502:17]
    end
    if (_ex_reg_valid_T | csr_io_interrupt | ibuf_io_inst_0_bits_replay) begin // @[RocketCore.scala 500:73]
      ex_reg_raw_inst <= ibuf_io_inst_0_bits_raw; // @[RocketCore.scala 503:21]
    end
    mem_reg_xcpt_interrupt <= _ex_reg_replay_T & ex_reg_xcpt_interrupt; // @[RocketCore.scala 548:45]
    mem_reg_valid <= ~ctrl_killx; // @[RocketCore.scala 545:20]
    if (!(mem_reg_valid & mem_reg_flush_pipe)) begin // @[RocketCore.scala 552:46]
      if (ex_pc_valid) begin // @[RocketCore.scala 554:28]
        mem_reg_rvc <= ex_reg_rvc; // @[RocketCore.scala 558:17]
      end
    end
    mem_reg_xcpt <= _mem_reg_valid_T & ex_xcpt; // @[RocketCore.scala 547:31]
    mem_reg_replay <= _ex_reg_replay_T & replay_ex; // @[RocketCore.scala 546:37]
    if (!(mem_reg_valid & mem_reg_flush_pipe)) begin // @[RocketCore.scala 552:46]
      if (ex_pc_valid) begin // @[RocketCore.scala 554:28]
        mem_reg_flush_pipe <= _GEN_80;
      end
    end
    if (!(mem_reg_valid & mem_reg_flush_pipe)) begin // @[RocketCore.scala 552:46]
      if (ex_pc_valid) begin // @[RocketCore.scala 554:28]
        mem_reg_cause <= ex_reg_cause; // @[RocketCore.scala 567:19]
      end
    end
    if (!(mem_reg_valid & mem_reg_flush_pipe)) begin // @[RocketCore.scala 552:46]
      if (ex_pc_valid) begin // @[RocketCore.scala 554:28]
        mem_reg_slow_bypass <= ex_slow_bypass; // @[RocketCore.scala 564:25]
      end
    end
    if (!(mem_reg_valid & mem_reg_flush_pipe)) begin // @[RocketCore.scala 552:46]
      if (ex_pc_valid) begin // @[RocketCore.scala 554:28]
        mem_reg_load <= ex_ctrl_mem & _mem_reg_load_T_24; // @[RocketCore.scala 559:18]
      end
    end
    if (!(mem_reg_valid & mem_reg_flush_pipe)) begin // @[RocketCore.scala 552:46]
      if (ex_pc_valid) begin // @[RocketCore.scala 554:28]
        mem_reg_store <= ex_ctrl_mem & _mem_reg_store_T_22; // @[RocketCore.scala 560:19]
      end
    end
    if (!(mem_reg_valid & mem_reg_flush_pipe)) begin // @[RocketCore.scala 552:46]
      if (ex_pc_valid) begin // @[RocketCore.scala 554:28]
        mem_reg_pc <= ex_reg_pc; // @[RocketCore.scala 572:16]
      end
    end
    if (!(mem_reg_valid & mem_reg_flush_pipe)) begin // @[RocketCore.scala 552:46]
      if (ex_pc_valid) begin // @[RocketCore.scala 554:28]
        mem_reg_inst <= ex_reg_inst; // @[RocketCore.scala 568:18]
      end
    end
    if (!(mem_reg_valid & mem_reg_flush_pipe)) begin // @[RocketCore.scala 552:46]
      if (ex_pc_valid) begin // @[RocketCore.scala 554:28]
        mem_reg_hls_or_dv <= io_dmem_req_bits_dv; // @[RocketCore.scala 571:23]
      end
    end
    if (!(mem_reg_valid & mem_reg_flush_pipe)) begin // @[RocketCore.scala 552:46]
      if (ex_pc_valid) begin // @[RocketCore.scala 554:28]
        mem_reg_raw_inst <= ex_reg_raw_inst; // @[RocketCore.scala 569:22]
      end
    end
    if (!(mem_reg_valid & mem_reg_flush_pipe)) begin // @[RocketCore.scala 552:46]
      if (ex_pc_valid) begin // @[RocketCore.scala 554:28]
        mem_reg_wdata <= _mem_reg_wdata_T; // @[RocketCore.scala 573:19]
      end
    end
    if (!(mem_reg_valid & mem_reg_flush_pipe)) begin // @[RocketCore.scala 552:46]
      if (ex_pc_valid) begin // @[RocketCore.scala 554:28]
        if (ex_ctrl_rxs2 & (ex_ctrl_mem | ex_ctrl_rocc)) begin // @[RocketCore.scala 576:71]
          if (size == 2'h0) begin // @[AMOALU.scala 27:13]
            mem_reg_rs2 <= _mem_reg_rs2_T_3;
          end else begin
            mem_reg_rs2 <= _mem_reg_rs2_T_7;
          end
        end
      end
    end
    if (!(mem_reg_valid & mem_reg_flush_pipe)) begin // @[RocketCore.scala 552:46]
      if (ex_pc_valid) begin // @[RocketCore.scala 554:28]
        mem_br_taken <= alu_io_cmp_out; // @[RocketCore.scala 574:18]
      end
    end
    wb_reg_valid <= ~ctrl_killm; // @[RocketCore.scala 613:19]
    wb_reg_xcpt <= mem_xcpt & _wb_reg_replay_T; // @[RocketCore.scala 615:27]
    wb_reg_replay <= replay_mem & ~take_pc_wb; // @[RocketCore.scala 614:31]
    wb_reg_flush_pipe <= _wb_reg_valid_T & mem_reg_flush_pipe; // @[RocketCore.scala 616:36]
    if (mem_pc_valid) begin // @[RocketCore.scala 617:23]
      if (_T_70) begin // @[Mux.scala 47:70]
        wb_reg_cause <= mem_reg_cause;
      end else begin
        wb_reg_cause <= {{28'd0}, _T_74};
      end
    end
    if (mem_pc_valid) begin // @[RocketCore.scala 617:23]
      wb_reg_pc <= mem_reg_pc; // @[RocketCore.scala 632:15]
    end
    if (mem_pc_valid) begin // @[RocketCore.scala 617:23]
      wb_reg_hls_or_dv <= mem_reg_hls_or_dv; // @[RocketCore.scala 629:22]
    end
    if (mem_pc_valid) begin // @[RocketCore.scala 617:23]
      wb_reg_inst <= mem_reg_inst; // @[RocketCore.scala 626:17]
    end
    if (mem_pc_valid) begin // @[RocketCore.scala 617:23]
      wb_reg_raw_inst <= mem_reg_raw_inst; // @[RocketCore.scala 627:21]
    end
    if (mem_pc_valid) begin // @[RocketCore.scala 617:23]
      if (_take_pc_mem_T & mem_ctrl_fp & mem_ctrl_wxd) begin // @[RocketCore.scala 621:10]
        wb_reg_wdata <= 32'h0;
      end else begin
        wb_reg_wdata <= mem_int_wdata;
      end
    end
    if (reset) begin // @[RocketCore.scala 285:25]
      id_reg_fence <= 1'h0; // @[RocketCore.scala 285:25]
    end else if (_ex_reg_valid_T) begin // @[RocketCore.scala 444:22]
      id_reg_fence <= _GEN_2;
    end else if (~id_mem_busy) begin // @[RocketCore.scala 329:23]
      id_reg_fence <= 1'h0; // @[RocketCore.scala 329:38]
    end
    if (_ex_reg_valid_T) begin // @[RocketCore.scala 444:22]
      if (id_illegal_insn) begin // @[RocketCore.scala 493:47]
        ex_reg_rs_bypass_0 <= 1'h0; // @[RocketCore.scala 495:27]
      end else begin
        ex_reg_rs_bypass_0 <= do_bypass; // @[RocketCore.scala 486:27]
      end
    end
    if (_ex_reg_valid_T) begin // @[RocketCore.scala 444:22]
      ex_reg_rs_bypass_1 <= do_bypass_1; // @[RocketCore.scala 486:27]
    end
    if (_ex_reg_valid_T) begin // @[RocketCore.scala 444:22]
      if (id_illegal_insn) begin // @[RocketCore.scala 493:47]
        ex_reg_rs_lsb_0 <= inst[1:0]; // @[RocketCore.scala 496:24]
      end else if (id_ctrl_decoder_7 & ~do_bypass) begin // @[RocketCore.scala 488:38]
        ex_reg_rs_lsb_0 <= id_rs_0[1:0]; // @[RocketCore.scala 489:26]
      end else if (id_bypass_src_0_0) begin // @[Mux.scala 47:70]
        ex_reg_rs_lsb_0 <= 2'h0;
      end else begin
        ex_reg_rs_lsb_0 <= _bypass_src_T_1;
      end
    end
    if (_ex_reg_valid_T) begin // @[RocketCore.scala 444:22]
      if (id_ctrl_decoder_6 & ~do_bypass_1) begin // @[RocketCore.scala 488:38]
        ex_reg_rs_lsb_1 <= id_rs_1[1:0]; // @[RocketCore.scala 489:26]
      end else if (id_bypass_src_1_0) begin // @[Mux.scala 47:70]
        ex_reg_rs_lsb_1 <= 2'h0;
      end else if (id_bypass_src_1_1) begin // @[Mux.scala 47:70]
        ex_reg_rs_lsb_1 <= 2'h1;
      end else begin
        ex_reg_rs_lsb_1 <= _bypass_src_T_2;
      end
    end
    if (_ex_reg_valid_T) begin // @[RocketCore.scala 444:22]
      if (id_illegal_insn) begin // @[RocketCore.scala 493:47]
        ex_reg_rs_msb_0 <= inst[31:2]; // @[RocketCore.scala 497:24]
      end else if (id_ctrl_decoder_7 & ~do_bypass) begin // @[RocketCore.scala 488:38]
        ex_reg_rs_msb_0 <= id_rs_0[31:2]; // @[RocketCore.scala 490:26]
      end
    end
    if (_ex_reg_valid_T) begin // @[RocketCore.scala 444:22]
      if (id_ctrl_decoder_6 & ~do_bypass_1) begin // @[RocketCore.scala 488:38]
        ex_reg_rs_msb_1 <= id_rs_1[31:2]; // @[RocketCore.scala 490:26]
      end
    end
    if (reset) begin // @[RocketCore.scala 1050:25]
      _r <= 32'h0; // @[RocketCore.scala 1050:25]
    end else if (_T_149) begin // @[RocketCore.scala 1058:18]
      _r <= _T_148; // @[RocketCore.scala 1058:23]
    end else if (ll_wen) begin // @[RocketCore.scala 1058:18]
      _r <= _T_143; // @[RocketCore.scala 1058:23]
    end
    blocked <= _replay_ex_structural_T & _dcache_blocked_T & (blocked | io_dmem_req_valid | io_dmem_s2_nack); // @[RocketCore.scala 810:83]
    rocc_blocked <= _wb_valid_T_2 & (io_rocc_cmd_valid | rocc_blocked); // @[RocketCore.scala 814:50]
    div_io_kill_REG <= div_io_req_ready & div_io_req_valid; // @[Decoupled.scala 50:35]
    if (ex_reg_rs_bypass_0) begin // @[RocketCore.scala 391:14]
      if (ex_reg_rs_lsb_0 == 2'h3) begin // @[package.scala 32:76]
        coreMonitorBundle_rd0val_x23 <= io_dmem_resp_bits_data_word_bypass;
      end else if (ex_reg_rs_lsb_0 == 2'h2) begin // @[package.scala 32:76]
        coreMonitorBundle_rd0val_x23 <= wb_reg_wdata;
      end else if (ex_reg_rs_lsb_0 == 2'h1) begin // @[package.scala 32:76]
        coreMonitorBundle_rd0val_x23 <= mem_reg_wdata;
      end else begin
        coreMonitorBundle_rd0val_x23 <= 32'h0;
      end
    end else begin
      coreMonitorBundle_rd0val_x23 <= _ex_rs_T_6;
    end
    coreMonitorBundle_rd0val_REG <= coreMonitorBundle_rd0val_x23; // @[RocketCore.scala 945:34]
    if (ex_reg_rs_bypass_1) begin // @[RocketCore.scala 391:14]
      if (ex_reg_rs_lsb_1 == 2'h3) begin // @[package.scala 32:76]
        coreMonitorBundle_rd1val_x29 <= io_dmem_resp_bits_data_word_bypass;
      end else if (ex_reg_rs_lsb_1 == 2'h2) begin // @[package.scala 32:76]
        coreMonitorBundle_rd1val_x29 <= wb_reg_wdata;
      end else if (ex_reg_rs_lsb_1 == 2'h1) begin // @[package.scala 32:76]
        coreMonitorBundle_rd1val_x29 <= mem_reg_wdata;
      end else begin
        coreMonitorBundle_rd1val_x29 <= 32'h0;
      end
    end else begin
      coreMonitorBundle_rd1val_x29 <= _ex_rs_T_13;
    end
    coreMonitorBundle_rd1val_REG <= coreMonitorBundle_rd1val_x29; // @[RocketCore.scala 947:34]
    `ifndef SYNTHESIS
    `ifdef STOP_COND
      if (`STOP_COND) begin
    `endif
        if (~(~htval_valid_imem) & ~reset) begin
          $fatal; // @[RocketCore.scala 735:11]
        end
    `ifdef STOP_COND
      end
    `endif
    `endif // SYNTHESIS
    `ifndef SYNTHESIS
    `ifdef PRINTF_COND
      if (`PRINTF_COND) begin
    `endif
        if (~reset & ~(~htval_valid_imem)) begin
          $fwrite(32'h80000002,
            "Assertion failed\n    at RocketCore.scala:735 assert(!htval_valid_imem || io.imem.gpa.valid)\n"); // @[RocketCore.scala 735:11]
        end
    `ifdef PRINTF_COND
      end
    `endif
    `endif // SYNTHESIS
    `ifndef SYNTHESIS
    `ifdef PRINTF_COND
      if (`PRINTF_COND) begin
    `endif
        if (csr_io_trace_0_valid & _csr_io_htval_T_3) begin
          $fwrite(32'h80000002,"C%d: %d [%d] pc=[%x] W[r%d=%x][%d] R[r%d=%x] R[r%d=%x] inst=[%x] DASM(%x)\n",io_hartid,
            _io_fpu_time_T,coreMonitorBundle_valid,coreMonitorBundle_pc,_T_151,_T_152,coreMonitorBundle_wrenx,_T_154,
            _T_156,_T_158,_T_160,coreMonitorBundle_inst,coreMonitorBundle_inst); // @[RocketCore.scala 980:13]
        end
    `ifdef PRINTF_COND
      end
    `endif
    `endif // SYNTHESIS
  end
// Register and memory initialization
`ifdef RANDOMIZE_GARBAGE_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_INVALID_ASSIGN
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_REG_INIT
`define RANDOMIZE
`endif
`ifdef RANDOMIZE_MEM_INIT
`define RANDOMIZE
`endif
`ifndef RANDOM
`define RANDOM $random
`endif
`ifdef RANDOMIZE_MEM_INIT
  integer initvar;
`endif
`ifndef SYNTHESIS
`ifdef FIRRTL_BEFORE_INITIAL
`FIRRTL_BEFORE_INITIAL
`endif
initial begin
  `ifdef RANDOMIZE
    `ifdef INIT_RANDOM
      `INIT_RANDOM
    `endif
    `ifndef VERILATOR
      `ifdef RANDOMIZE_DELAY
        #`RANDOMIZE_DELAY begin end
      `else
        #0.002 begin end
      `endif
    `endif
`ifdef RANDOMIZE_GARBAGE_ASSIGN
  _RAND_1 = {1{`RANDOM}};
  _RAND_2 = {1{`RANDOM}};
`endif // RANDOMIZE_GARBAGE_ASSIGN
`ifdef RANDOMIZE_MEM_INIT
  _RAND_0 = {1{`RANDOM}};
  for (initvar = 0; initvar < 31; initvar = initvar+1)
    rf[initvar] = _RAND_0[31:0];
`endif // RANDOMIZE_MEM_INIT
`ifdef RANDOMIZE_REG_INIT
  _RAND_3 = {1{`RANDOM}};
  id_reg_pause = _RAND_3[0:0];
  _RAND_4 = {1{`RANDOM}};
  imem_might_request_reg = _RAND_4[0:0];
  _RAND_5 = {1{`RANDOM}};
  ex_ctrl_fp = _RAND_5[0:0];
  _RAND_6 = {1{`RANDOM}};
  ex_ctrl_rocc = _RAND_6[0:0];
  _RAND_7 = {1{`RANDOM}};
  ex_ctrl_branch = _RAND_7[0:0];
  _RAND_8 = {1{`RANDOM}};
  ex_ctrl_jal = _RAND_8[0:0];
  _RAND_9 = {1{`RANDOM}};
  ex_ctrl_jalr = _RAND_9[0:0];
  _RAND_10 = {1{`RANDOM}};
  ex_ctrl_rxs2 = _RAND_10[0:0];
  _RAND_11 = {1{`RANDOM}};
  ex_ctrl_rxs1 = _RAND_11[0:0];
  _RAND_12 = {1{`RANDOM}};
  ex_ctrl_sel_alu2 = _RAND_12[1:0];
  _RAND_13 = {1{`RANDOM}};
  ex_ctrl_sel_alu1 = _RAND_13[1:0];
  _RAND_14 = {1{`RANDOM}};
  ex_ctrl_sel_imm = _RAND_14[2:0];
  _RAND_15 = {1{`RANDOM}};
  ex_ctrl_alu_fn = _RAND_15[3:0];
  _RAND_16 = {1{`RANDOM}};
  ex_ctrl_mem = _RAND_16[0:0];
  _RAND_17 = {1{`RANDOM}};
  ex_ctrl_mem_cmd = _RAND_17[4:0];
  _RAND_18 = {1{`RANDOM}};
  ex_ctrl_rfs1 = _RAND_18[0:0];
  _RAND_19 = {1{`RANDOM}};
  ex_ctrl_rfs2 = _RAND_19[0:0];
  _RAND_20 = {1{`RANDOM}};
  ex_ctrl_wfd = _RAND_20[0:0];
  _RAND_21 = {1{`RANDOM}};
  ex_ctrl_mul = _RAND_21[0:0];
  _RAND_22 = {1{`RANDOM}};
  ex_ctrl_div = _RAND_22[0:0];
  _RAND_23 = {1{`RANDOM}};
  ex_ctrl_wxd = _RAND_23[0:0];
  _RAND_24 = {1{`RANDOM}};
  ex_ctrl_csr = _RAND_24[2:0];
  _RAND_25 = {1{`RANDOM}};
  ex_ctrl_fence_i = _RAND_25[0:0];
  _RAND_26 = {1{`RANDOM}};
  mem_ctrl_fp = _RAND_26[0:0];
  _RAND_27 = {1{`RANDOM}};
  mem_ctrl_rocc = _RAND_27[0:0];
  _RAND_28 = {1{`RANDOM}};
  mem_ctrl_branch = _RAND_28[0:0];
  _RAND_29 = {1{`RANDOM}};
  mem_ctrl_jal = _RAND_29[0:0];
  _RAND_30 = {1{`RANDOM}};
  mem_ctrl_jalr = _RAND_30[0:0];
  _RAND_31 = {1{`RANDOM}};
  mem_ctrl_rxs2 = _RAND_31[0:0];
  _RAND_32 = {1{`RANDOM}};
  mem_ctrl_rxs1 = _RAND_32[0:0];
  _RAND_33 = {1{`RANDOM}};
  mem_ctrl_mem = _RAND_33[0:0];
  _RAND_34 = {1{`RANDOM}};
  mem_ctrl_rfs1 = _RAND_34[0:0];
  _RAND_35 = {1{`RANDOM}};
  mem_ctrl_rfs2 = _RAND_35[0:0];
  _RAND_36 = {1{`RANDOM}};
  mem_ctrl_wfd = _RAND_36[0:0];
  _RAND_37 = {1{`RANDOM}};
  mem_ctrl_mul = _RAND_37[0:0];
  _RAND_38 = {1{`RANDOM}};
  mem_ctrl_div = _RAND_38[0:0];
  _RAND_39 = {1{`RANDOM}};
  mem_ctrl_wxd = _RAND_39[0:0];
  _RAND_40 = {1{`RANDOM}};
  mem_ctrl_csr = _RAND_40[2:0];
  _RAND_41 = {1{`RANDOM}};
  mem_ctrl_fence_i = _RAND_41[0:0];
  _RAND_42 = {1{`RANDOM}};
  wb_ctrl_rocc = _RAND_42[0:0];
  _RAND_43 = {1{`RANDOM}};
  wb_ctrl_rxs2 = _RAND_43[0:0];
  _RAND_44 = {1{`RANDOM}};
  wb_ctrl_rxs1 = _RAND_44[0:0];
  _RAND_45 = {1{`RANDOM}};
  wb_ctrl_mem = _RAND_45[0:0];
  _RAND_46 = {1{`RANDOM}};
  wb_ctrl_rfs1 = _RAND_46[0:0];
  _RAND_47 = {1{`RANDOM}};
  wb_ctrl_rfs2 = _RAND_47[0:0];
  _RAND_48 = {1{`RANDOM}};
  wb_ctrl_wfd = _RAND_48[0:0];
  _RAND_49 = {1{`RANDOM}};
  wb_ctrl_div = _RAND_49[0:0];
  _RAND_50 = {1{`RANDOM}};
  wb_ctrl_wxd = _RAND_50[0:0];
  _RAND_51 = {1{`RANDOM}};
  wb_ctrl_csr = _RAND_51[2:0];
  _RAND_52 = {1{`RANDOM}};
  wb_ctrl_fence_i = _RAND_52[0:0];
  _RAND_53 = {1{`RANDOM}};
  ex_reg_xcpt_interrupt = _RAND_53[0:0];
  _RAND_54 = {1{`RANDOM}};
  ex_reg_valid = _RAND_54[0:0];
  _RAND_55 = {1{`RANDOM}};
  ex_reg_rvc = _RAND_55[0:0];
  _RAND_56 = {1{`RANDOM}};
  ex_reg_xcpt = _RAND_56[0:0];
  _RAND_57 = {1{`RANDOM}};
  ex_reg_flush_pipe = _RAND_57[0:0];
  _RAND_58 = {1{`RANDOM}};
  ex_reg_load_use = _RAND_58[0:0];
  _RAND_59 = {1{`RANDOM}};
  ex_reg_cause = _RAND_59[31:0];
  _RAND_60 = {1{`RANDOM}};
  ex_reg_replay = _RAND_60[0:0];
  _RAND_61 = {1{`RANDOM}};
  ex_reg_pc = _RAND_61[31:0];
  _RAND_62 = {1{`RANDOM}};
  ex_reg_mem_size = _RAND_62[1:0];
  _RAND_63 = {1{`RANDOM}};
  ex_reg_inst = _RAND_63[31:0];
  _RAND_64 = {1{`RANDOM}};
  ex_reg_raw_inst = _RAND_64[31:0];
  _RAND_65 = {1{`RANDOM}};
  mem_reg_xcpt_interrupt = _RAND_65[0:0];
  _RAND_66 = {1{`RANDOM}};
  mem_reg_valid = _RAND_66[0:0];
  _RAND_67 = {1{`RANDOM}};
  mem_reg_rvc = _RAND_67[0:0];
  _RAND_68 = {1{`RANDOM}};
  mem_reg_xcpt = _RAND_68[0:0];
  _RAND_69 = {1{`RANDOM}};
  mem_reg_replay = _RAND_69[0:0];
  _RAND_70 = {1{`RANDOM}};
  mem_reg_flush_pipe = _RAND_70[0:0];
  _RAND_71 = {1{`RANDOM}};
  mem_reg_cause = _RAND_71[31:0];
  _RAND_72 = {1{`RANDOM}};
  mem_reg_slow_bypass = _RAND_72[0:0];
  _RAND_73 = {1{`RANDOM}};
  mem_reg_load = _RAND_73[0:0];
  _RAND_74 = {1{`RANDOM}};
  mem_reg_store = _RAND_74[0:0];
  _RAND_75 = {1{`RANDOM}};
  mem_reg_pc = _RAND_75[31:0];
  _RAND_76 = {1{`RANDOM}};
  mem_reg_inst = _RAND_76[31:0];
  _RAND_77 = {1{`RANDOM}};
  mem_reg_hls_or_dv = _RAND_77[0:0];
  _RAND_78 = {1{`RANDOM}};
  mem_reg_raw_inst = _RAND_78[31:0];
  _RAND_79 = {1{`RANDOM}};
  mem_reg_wdata = _RAND_79[31:0];
  _RAND_80 = {1{`RANDOM}};
  mem_reg_rs2 = _RAND_80[31:0];
  _RAND_81 = {1{`RANDOM}};
  mem_br_taken = _RAND_81[0:0];
  _RAND_82 = {1{`RANDOM}};
  wb_reg_valid = _RAND_82[0:0];
  _RAND_83 = {1{`RANDOM}};
  wb_reg_xcpt = _RAND_83[0:0];
  _RAND_84 = {1{`RANDOM}};
  wb_reg_replay = _RAND_84[0:0];
  _RAND_85 = {1{`RANDOM}};
  wb_reg_flush_pipe = _RAND_85[0:0];
  _RAND_86 = {1{`RANDOM}};
  wb_reg_cause = _RAND_86[31:0];
  _RAND_87 = {1{`RANDOM}};
  wb_reg_pc = _RAND_87[31:0];
  _RAND_88 = {1{`RANDOM}};
  wb_reg_hls_or_dv = _RAND_88[0:0];
  _RAND_89 = {1{`RANDOM}};
  wb_reg_inst = _RAND_89[31:0];
  _RAND_90 = {1{`RANDOM}};
  wb_reg_raw_inst = _RAND_90[31:0];
  _RAND_91 = {1{`RANDOM}};
  wb_reg_wdata = _RAND_91[31:0];
  _RAND_92 = {1{`RANDOM}};
  id_reg_fence = _RAND_92[0:0];
  _RAND_93 = {1{`RANDOM}};
  ex_reg_rs_bypass_0 = _RAND_93[0:0];
  _RAND_94 = {1{`RANDOM}};
  ex_reg_rs_bypass_1 = _RAND_94[0:0];
  _RAND_95 = {1{`RANDOM}};
  ex_reg_rs_lsb_0 = _RAND_95[1:0];
  _RAND_96 = {1{`RANDOM}};
  ex_reg_rs_lsb_1 = _RAND_96[1:0];
  _RAND_97 = {1{`RANDOM}};
  ex_reg_rs_msb_0 = _RAND_97[29:0];
  _RAND_98 = {1{`RANDOM}};
  ex_reg_rs_msb_1 = _RAND_98[29:0];
  _RAND_99 = {1{`RANDOM}};
  _r = _RAND_99[31:0];
  _RAND_100 = {1{`RANDOM}};
  blocked = _RAND_100[0:0];
  _RAND_101 = {1{`RANDOM}};
  rocc_blocked = _RAND_101[0:0];
  _RAND_102 = {1{`RANDOM}};
  div_io_kill_REG = _RAND_102[0:0];
  _RAND_103 = {1{`RANDOM}};
  coreMonitorBundle_rd0val_x23 = _RAND_103[31:0];
  _RAND_104 = {1{`RANDOM}};
  coreMonitorBundle_rd0val_REG = _RAND_104[31:0];
  _RAND_105 = {1{`RANDOM}};
  coreMonitorBundle_rd1val_x29 = _RAND_105[31:0];
  _RAND_106 = {1{`RANDOM}};
  coreMonitorBundle_rd1val_REG = _RAND_106[31:0];
`endif // RANDOMIZE_REG_INIT
  `endif // RANDOMIZE
end // initial
`ifdef FIRRTL_AFTER_INITIAL
`FIRRTL_AFTER_INITIAL
`endif
`endif // SYNTHESIS
endmodule
