module inst_decoder_top
  (
   input wire i_clk,
   input wire i_rst
   );
   (*keep*)
   reg [31:0] inst;
   (*keep*)
   wire [31:0] immediate;
   (*keep*)
   wire [4:0]  a_rs1;
   (*keep*)
   wire [4:0]  a_rs2;
   (*keep*)
   wire [4:0]  a_rd;
   (*keep*)
   wire        inst_lui;
   (*keep*)
   wire        inst_auipc;
   (*keep*)
   wire        inst_jal;
   (*keep*)
   wire        inst_jalr;
   (*keep*)
   wire        inst_beq;
   (*keep*)
   wire        inst_bne;
   (*keep*)
   wire        inst_blt;
   (*keep*)
   wire        inst_bge;
   (*keep*)
   wire        inst_bltu;
   (*keep*)
   wire        inst_bgeu;
   (*keep*)
   wire        inst_lb;
   (*keep*)
   wire        inst_lh;
   (*keep*)
   wire        inst_lw;
   (*keep*)
   wire        inst_lbu;
   (*keep*)
   wire        inst_lhu;
   (*keep*)
   wire        inst_sb;
   (*keep*)
   wire        inst_sh;
   (*keep*)
   wire        inst_sw;
   (*keep*)
   wire        inst_addi;
   (*keep*)
   wire        inst_slti;
   (*keep*)
   wire        inst_sltiu;
   (*keep*)
   wire        inst_xori;
   (*keep*)
   wire        inst_ori;
   (*keep*)
   wire        inst_andi;
   (*keep*)
   wire        inst_slli;
   (*keep*)
   wire        inst_srli;
   (*keep*)
   wire        inst_srai; 
   (*keep*)
   wire        inst_add;
   (*keep*)
   wire        inst_sub;
   (*keep*)
   wire        inst_sll;
   (*keep*)
   wire        inst_slt;
   (*keep*)
   wire        inst_sltu;
   (*keep*)
   wire        inst_xor;
   (*keep*)
   wire        inst_srl;
   (*keep*)
   wire        inst_sra;
   (*keep*)
   wire        inst_or;
   (*keep*)
   wire        inst_and;
   (*keep*)
   wire        inst_fence;
   (*keep*)
   wire        inst_fence_i;
   (*keep*)
   wire        inst_ecall;
   (*keep*)
   wire        inst_ebreak;
   (*keep*)
   wire        inst_csrrw;
   (*keep*)
   wire        inst_csrrs;
   (*keep*)
   wire        inst_csrrc;
   (*keep*)
   wire        inst_csrrwi;
   (*keep*)
   wire        inst_csrrsi;
   (*keep*)
   wire        inst_csrrci;
   (*keep*)
   wire        inst_illegal;
   
   inst_decoder dec0
     (
      .i_inst(inst)
      , .o_immediate(immediate)
      , .o_a_rs1(a_rs1)
      , .o_a_rs2(a_rs2)
      , .o_a_rd(a_rd)
      , .o_inst_lui(inst_lui)
      , .o_inst_auipc(inst_auipc)
      , .o_inst_jal(inst_jal)
      , .o_inst_jalr(inst_jalr)
      , .o_inst_beq(inst_beq)
      , .o_inst_bne(inst_bne)
      , .o_inst_blt(inst_blt)
      , .o_inst_bge(inst_bge)
      , .o_inst_bltu(inst_bltu)
      , .o_inst_bgeu(inst_bgeu)
      , .o_inst_lb(inst_lb)
      , .o_inst_lh(inst_lh)
      , .o_inst_lw(inst_lw)
      , .o_inst_lbu(inst_lbu)
      , .o_inst_lhu(inst_lhu)
      , .o_inst_sb(inst_sb)
      , .o_inst_sh(inst_sh)
      , .o_inst_sw(inst_sw)
      , .o_inst_addi(inst_addi)
      , .o_inst_slti(inst_slti)
      , .o_inst_sltiu(inst_sltiu)
      , .o_inst_xori(inst_xori)
      , .o_inst_ori(inst_ori)
      , .o_inst_andi(inst_andi)
      , .o_inst_slli(inst_slli)
      , .o_inst_srli(inst_srli)
      , .o_inst_srai(inst_srai) 
      , .o_inst_add(inst_add)
      , .o_inst_sub(inst_sub)
      , .o_inst_sll(inst_sll)
      , .o_inst_slt(inst_slt)
      , .o_inst_sltu(inst_sltu)
      , .o_inst_xor(inst_xor)
      , .o_inst_srl(inst_srl)
      , .o_inst_sra(inst_sra)
      , .o_inst_or(inst_or)
      , .o_inst_and(inst_and)
      , .o_inst_fence(inst_fence)
      , .o_inst_fence_i(inst_fence_i)
      , .o_inst_ecall(inst_ecall)
      , .o_inst_ebreak(inst_ebreak)
      , .o_inst_csrrw(inst_csrrw)
      , .o_inst_csrrs(inst_csrrs)
      , .o_inst_csrrc(inst_csrrc)
      , .o_inst_csrrwi(inst_csrrwi)
      , .o_inst_csrrsi(inst_csrrsi)
      , .o_inst_csrrci(inst_csrrci)
      , .o_inst_illegal(inst_illegal)
      );

   always @ ( posedge i_clk ) begin
      if (i_rst) begin
	 inst <= 32'b0;
      end
      else begin
	 inst <= inst + 32'b1;
      end
   end
   
endmodule
