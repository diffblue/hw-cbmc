//////////////////////////////////////////////////////////////////////
////                                                              ////
////  OR1200's instruction fetch                                  ////
////                                                              ////
////  This file is part of the OpenRISC 1200 project              ////
////  http://www.opencores.org/project,or1k                       ////
////                                                              ////
////  Description                                                 ////
////  PC, instruction fetch, interface to IC.                     ////
////                                                              ////
////  To Do:                                                      ////
////   - make it smaller and faster                               ////
////                                                              ////
////  Author(s):                                                  ////
////      - Damjan Lampret, lampret@opencores.org                 ////
////                                                              ////
//////////////////////////////////////////////////////////////////////
////                                                              ////
//// Copyright (C) 2000 Authors and OPENCORES.ORG                 ////
////                                                              ////
//// This source file may be used and distributed without         ////
//// restriction provided that this copyright statement is not    ////
//// removed from the file and that any derivative work contains  ////
//// the original copyright notice and the associated disclaimer. ////
////                                                              ////
//// This source file is free software; you can redistribute it   ////
//// and/or modify it under the terms of the GNU Lesser General   ////
//// Public License as published by the Free Software Foundation; ////
//// either version 2.1 of the License, or (at your option) any   ////
//// later version.                                               ////
////                                                              ////
//// This source is distributed in the hope that it will be       ////
//// useful, but WITHOUT ANY WARRANTY; without even the implied   ////
//// warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR      ////
//// PURPOSE.  See the GNU Lesser General Public License for more ////
//// details.                                                     ////
////                                                              ////
//// You should have received a copy of the GNU Lesser General    ////
//// Public License along with this source; if not, download it   ////
//// from http://www.opencores.org/lgpl.shtml                     ////
////                                                              ////
//////////////////////////////////////////////////////////////////////
//
// $Log: or1200_if.v,v $
// Revision 2.0  2010/06/30 11:00:00  ORSoC
// Major update: 
// Structure reordered and bugs fixed. 

// synopsys translate_off
`include "timescale.v"
// synopsys translate_on
`include "or1200_defines.v"

module or1200_if(
	// Clock and reset
	clk, rst,

	// External i/f to IC
	icpu_dat_i, icpu_ack_i, icpu_err_i, icpu_adr_i, icpu_tag_i,

	// Internal i/f
	if_freeze, if_insn, if_pc, if_flushpipe, saving_if_insn, 
	if_stall, no_more_dslot, genpc_refetch, rfe,
	except_itlbmiss, except_immufault, except_ibuserr, dependency_hazard_stall, same_stage_dslot, if_two_insns, if_two_insns_ic
);

//
// I/O
//

//
// Clock and reset
//
input				clk;
input				rst;

//
// External i/f to IC
//
input	[63:0]			icpu_dat_i; //modified for two insns
input				icpu_ack_i;
input				icpu_err_i;
input	[31:0]			icpu_adr_i;
input	[3:0]			icpu_tag_i;

//
// Internal i/f
//
input				if_freeze;
output	[63:0]			if_insn; //double width
output	[31:0]			if_pc;
input				if_flushpipe;
output				saving_if_insn;
output				if_stall;
input				no_more_dslot;
output				genpc_refetch;
input				rfe;
output				except_itlbmiss;
output				except_immufault;
output				except_ibuserr;
output  			if_two_insns;   
input 	                	dependency_hazard_stall;
input   			same_stage_dslot;
input 	         		if_two_insns_ic;
			
 
//
// Internal wires and regs
//
wire			save_insn;
wire			if_bypass;
reg			if_bypass_reg;
reg	[63:0]		insn_saved; //if_freezemodified for two insns
reg	[31:0]		addr_saved;
reg	[2:0]		err_saved;
reg			saved;
reg 			if_two_insns_saved;
	
assign save_insn = (icpu_ack_i | icpu_err_i) & if_freeze & !saved; 
assign saving_if_insn = !if_flushpipe & save_insn;

//
// IF bypass 
//
assign if_bypass = icpu_adr_i[0] ? 1'b0 : if_bypass_reg | if_flushpipe;
always @(posedge clk or `OR1200_RST_EVENT rst)
	if (rst == `OR1200_RST_VALUE)
		if_bypass_reg <=  1'b0;
	else
		if_bypass_reg <=  if_bypass;

//
// IF stage insn
//
assign if_insn = no_more_dslot | rfe | if_bypass ? {2{`OR1200_OR32_NOP, 26'h041_0000}} : saved ? insn_saved : icpu_ack_i ? icpu_dat_i : {2{`OR1200_OR32_NOP, 26'h061_0000}}; //161 is used for exceptions 
//The following has been modified to take into account the possibility of two insns
assign if_pc = saved ? addr_saved : {icpu_adr_i[31:2], 2'h0};
assign if_two_insns = saved? if_two_insns_saved : /*icpu_err_i ? 1'b0:*/ if_two_insns_ic;
   
//it appears if_stall seems to almost mirror if_freeze
//primary difference is that if if_freeze is high and an instruction is being saved, than if_stall will be low
//if_freeze is defined in the freeze.v file
//however if_freeze is dependent on if_stall and will also be high if if_stall is high and lsu_unstall is low
//however if_freeze can go high for other reasons including a lsu_stall
assign if_stall = !icpu_err_i & !icpu_ack_i & !saved;    
assign genpc_refetch = saved & icpu_ack_i; 
//I haven't found a reason to change these for two insns yet (three exception lines below) since the second insn will never straddle a page/bus
assign except_itlbmiss = no_more_dslot ? 1'b0 : saved ? err_saved[0] : icpu_err_i & (icpu_tag_i == `OR1200_ITAG_TE);
assign except_immufault = no_more_dslot ? 1'b0 : saved ? err_saved[1] : icpu_err_i & (icpu_tag_i == `OR1200_ITAG_PE);
assign except_ibuserr = no_more_dslot ? 1'b0 : saved ? err_saved[2] : icpu_err_i & (icpu_tag_i == `OR1200_ITAG_BE);
   
//
// Flag for saved insn/address
//
always @(posedge clk or `OR1200_RST_EVENT rst)
	if (rst == `OR1200_RST_VALUE)
		saved <=  1'b0;
	else if (if_flushpipe)
		saved <=  1'b0;
	else if (save_insn)
		saved <=  1'b1;
	else if (!if_freeze)
		saved <=  1'b0;

//
// Store fetched instruction - modified to ensure two insns saved and changed the nop type to 141
//
always @(posedge clk or `OR1200_RST_EVENT rst)
	if (rst == `OR1200_RST_VALUE)
		insn_saved <=  {2{`OR1200_OR32_NOP, 26'h141_0000}};
	else if (if_flushpipe)
		insn_saved <=  {2{`OR1200_OR32_NOP, 26'h141_0000}};
	else if (save_insn)
		insn_saved <=  icpu_err_i ? {2{`OR1200_OR32_NOP, 26'h141_0000}} : icpu_dat_i; //modified for two insns
	else if (!if_freeze)
		insn_saved <=  {2{`OR1200_OR32_NOP, 26'h141_0000}};

//
// Store fetched instruction's address
//
always @(posedge clk or `OR1200_RST_EVENT rst)
	if (rst == `OR1200_RST_VALUE)
		addr_saved <=  32'h00000000;
	else if (if_flushpipe)
		addr_saved <=  32'h00000000;
	else if (save_insn)
		addr_saved <=  {icpu_adr_i[31:2], 2'b00}; 
	else if (!if_freeze)
		addr_saved <=  {icpu_adr_i[31:2], 2'b00};


//
// Store fetched number of instructions
//
always @(posedge clk or `OR1200_RST_EVENT rst)
	if (rst == `OR1200_RST_VALUE)
		if_two_insns_saved <=  1'b0;
	else if (if_flushpipe)
		if_two_insns_saved <=  1'b0;
	else if (save_insn)
		if_two_insns_saved <=  icpu_err_i ? 1'b0 : if_two_insns_ic; 
	else if (!if_freeze)
		if_two_insns_saved <=  if_two_insns_ic;

   
//
// Store fetched instruction's error tags 
//
always @(posedge clk or `OR1200_RST_EVENT rst)
	if (rst == `OR1200_RST_VALUE)
		err_saved <=  3'b000;
	else if (if_flushpipe)
		err_saved <=  3'b000;
	else if (save_insn) begin
		err_saved[0] <=  icpu_err_i & (icpu_tag_i == `OR1200_ITAG_TE);
		err_saved[1] <=  icpu_err_i & (icpu_tag_i == `OR1200_ITAG_PE);
		err_saved[2] <=  icpu_err_i & (icpu_tag_i == `OR1200_ITAG_BE);
	end
	else if (!if_freeze)
		err_saved <=  3'b000;

endmodule
