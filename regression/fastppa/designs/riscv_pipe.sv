module riscv_pipe(
  input clk,
  input [31:0] instr_in,
  input [31:0] dmem_rdata,
  output reg [31:0] pc,
  output reg [31:0] dmem_addr,
  output reg [31:0] dmem_wdata,
  output reg dmem_we
);
  reg [31:0] if_id_pc, if_id_instr;
  reg [31:0] id_ex_pc, id_ex_rs1, id_ex_rs2, id_ex_imm;
  reg [4:0]  id_ex_rd, id_ex_funct;
  reg [2:0]  id_ex_op;
  reg [31:0] ex_mem_alu, ex_mem_rs2;
  reg [4:0]  ex_mem_rd;
  reg [2:0]  ex_mem_op;
  reg [31:0] mem_wb_data;
  reg [4:0]  mem_wb_rd;
  reg        mem_wb_we;
  reg [31:0] regs [0:31];
  wire [4:0] rs1_addr = if_id_instr[19:15];
  wire [4:0] rs2_addr = if_id_instr[24:20];
  wire [4:0] rd_addr  = if_id_instr[11:7];
  wire [6:0] opcode   = if_id_instr[6:0];
  wire [2:0] funct3   = if_id_instr[14:12];
  wire [31:0] imm_i   = {{20{if_id_instr[31]}}, if_id_instr[31:20]};

  reg [31:0] alu_result;
  always @(*) begin
    case (id_ex_funct[2:0])
      3'b000: alu_result = id_ex_rs1 + id_ex_imm;
      3'b001: alu_result = id_ex_rs1 << id_ex_imm[4:0];
      3'b010: alu_result = ($signed(id_ex_rs1) < $signed(id_ex_imm)) ? 32'd1 : 32'd0;
      3'b011: alu_result = (id_ex_rs1 < id_ex_imm) ? 32'd1 : 32'd0;
      3'b100: alu_result = id_ex_rs1 ^ id_ex_imm;
      3'b101: alu_result = id_ex_rs1 >> id_ex_imm[4:0];
      3'b110: alu_result = id_ex_rs1 | id_ex_imm;
      3'b111: alu_result = id_ex_rs1 & id_ex_imm;
    endcase
  end

  always @(posedge clk) begin
    pc <= pc + 32'd4;
    if_id_pc <= pc;
    if_id_instr <= instr_in;
    id_ex_pc <= if_id_pc;
    id_ex_rs1 <= regs[rs1_addr];
    id_ex_rs2 <= regs[rs2_addr];
    id_ex_rd <= rd_addr;
    id_ex_imm <= imm_i;
    id_ex_funct <= {funct3, 2'b0};
    id_ex_op <= opcode[4:2];
    ex_mem_alu <= alu_result;
    ex_mem_rs2 <= id_ex_rs2;
    ex_mem_rd <= id_ex_rd;
    ex_mem_op <= id_ex_op;
    dmem_addr <= ex_mem_alu;
    dmem_wdata <= ex_mem_rs2;
    dmem_we <= (ex_mem_op == 3'b010);
    mem_wb_data <= (ex_mem_op == 3'b000) ? dmem_rdata : ex_mem_alu;
    mem_wb_rd <= ex_mem_rd;
    mem_wb_we <= (ex_mem_op != 3'b010);
    if (mem_wb_we && mem_wb_rd != 5'd0)
      regs[mem_wb_rd] <= mem_wb_data;
  end
  initial pc = 32'd0;
endmodule
