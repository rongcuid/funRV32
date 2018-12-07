module inst_decoder
  (
   input wire [31:0]  i_inst,
   output wire [31:0] o_immediate,
   output wire [4:0]  o_a_rs1,
   output wire [4:0]  o_a_rs2,
   output wire [4:0]  o_a_rd,
   output wire 	      o_inst_lui,
   output wire 	      o_inst_auipc,
   output wire 	      o_inst_jal,
   output wire 	      o_inst_jalr,
   output wire 	      o_inst_beq,
   output wire 	      o_inst_bne,
   output wire 	      o_inst_blt,
   output wire 	      o_inst_bge,
   output wire 	      o_inst_bltu,
   output wire 	      o_inst_bgeu,
   output wire 	      o_inst_lb,
   output wire 	      o_inst_lh,
   output wire 	      o_inst_lw,
   output wire 	      o_inst_lbu,
   output wire 	      o_inst_lhu,
   output wire 	      o_inst_sb,
   output wire 	      o_inst_sh,
   output wire 	      o_inst_sw,
   output wire 	      o_inst_addi,
   output wire 	      o_inst_slti,
   output wire 	      o_inst_sltiu,
   output wire 	      o_inst_xori,
   output wire 	      o_inst_ori,
   output wire 	      o_inst_andi,
   output wire 	      o_inst_slli,
   output wire 	      o_inst_srli,
   output wire 	      o_inst_srai, 
   output wire 	      o_inst_add,
   output wire 	      o_inst_sub,
   output wire 	      o_inst_sll,
   output wire 	      o_inst_slt,
   output wire 	      o_inst_sltu,
   output wire 	      o_inst_xor,
   output wire 	      o_inst_srl,
   output wire 	      o_inst_sra,
   output wire 	      o_inst_or,
   output wire 	      o_inst_and,
   output wire 	      o_inst_fence,
   output wire 	      o_inst_fence_i,
   output wire 	      o_inst_ecall,
   output wire 	      o_inst_ebreak,
   output wire 	      o_inst_csrrw,
   output wire 	      o_inst_csrrs,
   output wire 	      o_inst_csrrc,
   output wire 	      o_inst_csrrwi,
   output wire 	      o_inst_csrrsi,
   output wire 	      o_inst_csrrci,
   output wire 	      o_inst_illegal
   );

   assign o_a_rs1 = i_inst[19:15];
   assign o_a_rs2 = i_inst[24:20];
   assign o_a_rd = i_inst[11:7];
   reg 		      cat_load, cat_store, cat_branch, cat_jalr, cat_miscmem,
		      cat_jal, cat_opimm, cat_op, cat_system, cat_auipc, cat_lui,
		      cat_illegal;

   always @ (*) begin : CATEGORY
      cat_load = 1'b0;
      cat_store = 1'b0;
      cat_branch = 1'b0;
      cat_jalr = 1'b0;
      cat_miscmem = 1'b0;
      cat_jal = 1'b0;
      cat_opimm = 1'b0;
      cat_op = 1'b0;
      cat_system = 1'b0;
      cat_auipc = 1'b0;
      cat_lui = 1'b0;
      cat_illegal = 1'b0;
      case (i_inst[6:2])
	5'b00000: cat_load = 1'b1;
	5'b01000: cat_store = 1'b1;
	5'b11000: cat_branch = 1'b1;
	5'b11001: cat_jalr = 1'b1;
	5'b00011: cat_miscmem = 1'b1;
	5'b11011: cat_jal = 1'b1;
	5'b00100: cat_opimm = 1'b1;
	5'b01100: cat_op = 1'b1;
	5'b11100: cat_system = 1'b1;
	5'b00101: cat_auipc = 1'b1;
	5'b01101: cat_lui = 1'b1;
	default: cat_illegal = 1'b1;
      endcase // case (inst[6:2])
   end // block: CATEGORY

   wire imm_i, imm_s, imm_b, imm_u, imm_j;
   assign imm_i = cat_opimm | cat_jalr | cat_load | cat_miscmem | cat_system;
   assign imm_s = cat_store;
   assign imm_b = cat_branch;
   assign imm_u = cat_lui | cat_auipc;
   assign imm_j = cat_jal;

   assign o_immediate
     = imm_i ? { {21{i_inst[31]}}, i_inst[30:20] }
       : imm_s ? { {21{i_inst[31]}}, i_inst[30:25], i_inst[11:7] }
       : imm_b ? { {20{i_inst[31]}}, i_inst[7], i_inst[30:25], i_inst[11:8], 1'b0 }
       : imm_u ? { i_inst[31:12], 12'b0 }
       : imm_j ? { {12{i_inst[31]}}, i_inst[19:12], i_inst[20], i_inst[30:21], 1'b0 }
       : 32'bX;

   wire [2:0] funct3;
   wire [6:0] funct7;
   assign funct3 = i_inst[14:12];
   assign funct7 = i_inst[31:25];


   assign o_inst_lui = cat_lui;
   assign o_inst_auipc = cat_auipc;
   assign o_inst_jal = cat_jal;
   assign o_inst_jalr = cat_jalr;
   assign o_inst_beq = cat_branch && funct3 == 3'b000;
   assign o_inst_bne = cat_branch && funct3 == 3'b001;
   assign o_inst_blt = cat_branch && funct3 == 3'b100;
   assign o_inst_bge = cat_branch && funct3 == 3'b101;
   assign o_inst_bltu = cat_branch && funct3 == 3'b110;
   assign o_inst_bgeu = cat_branch && funct3 == 3'b111;
   assign o_inst_lb = cat_load && funct3 == 3'b000;
   assign o_inst_lh = cat_load && funct3 == 3'b001;
   assign o_inst_lw = cat_load && funct3 == 3'b010;
   assign o_inst_lbu = cat_load && funct3 == 3'b100;
   assign o_inst_lhu = cat_load && funct3 == 3'b101;
   assign o_inst_sb = cat_store && funct3 == 3'b000;
   assign o_inst_sh = cat_store && funct3 == 3'b001;
   assign o_inst_sw = cat_store && funct3 == 3'b010;
   assign o_inst_addi = cat_opimm && funct3 == 3'b000;
   assign o_inst_slti = cat_opimm && funct3 == 3'b010;
   assign o_inst_sltiu = cat_opimm && funct3 == 3'b011;
   assign o_inst_xori = cat_opimm && funct3 == 3'b100;
   assign o_inst_ori = cat_opimm && funct3 == 3'b110;
   assign o_inst_andi = cat_opimm && funct3 == 3'b111;
   assign o_inst_slli = cat_opimm && funct3 == 3'b001;
   assign o_inst_srli = cat_opimm && funct3 == 3'b101 && !funct7[5];
   assign o_inst_srai = cat_opimm && funct3 == 3'b101 && funct7[5];
   assign o_inst_add = cat_op && funct3 == 3'b000 && !funct7[5];
   assign o_inst_sub = cat_op && funct3 == 3'b000 && funct7[5];
   assign o_inst_sll = cat_op && funct3 == 3'b001;
   assign o_inst_slt = cat_op && funct3 == 3'b010;
   assign o_inst_sltu = cat_op && funct3 == 3'b011;
   assign o_inst_xor = cat_op && funct3 == 3'b100;
   assign o_inst_srl = cat_op && funct3 == 3'b101 && !funct7[5];
   assign o_inst_sra = cat_op && funct3 == 3'b101 && funct7[5];
   assign o_inst_or = cat_op && funct3 == 3'b110;
   assign o_inst_and = cat_op && funct3 == 3'b111;
   assign o_inst_fence = cat_miscmem && funct3 == 3'b000;
   assign o_inst_fence_i = cat_miscmem && funct3 == 3'b001;
   assign o_inst_ecall = cat_system && funct3 == 3'b000 && !o_a_rs2[0];
   assign o_inst_ebreak = cat_system && funct3 == 3'b000 && o_a_rs2[0];
   assign o_inst_csrrw = cat_system && funct3 == 3'b001;
   assign o_inst_csrrs = cat_system && funct3 == 3'b010;
   assign o_inst_csrrc = cat_system && funct3 == 3'b011;   
   assign o_inst_csrrwi = cat_system && funct3 == 3'b101;   
   assign o_inst_csrrsi = cat_system && funct3 == 3'b110;   
   assign o_inst_csrrci = cat_system && funct3 == 3'b111;

   assign o_inst_illegal
     = cat_illegal ||
       !(&{
    	   o_inst_lui,
    	   o_inst_auipc,
    	   o_inst_jal,
    	   o_inst_jalr,
    	   o_inst_beq,
    	   o_inst_bne,
    	   o_inst_blt,
    	   o_inst_bge,
    	   o_inst_bltu,
    	   o_inst_bgeu,
    	   o_inst_lb,
    	   o_inst_lh,
    	   o_inst_lw,
    	   o_inst_lbu,
    	   o_inst_lhu,
    	   o_inst_sb,
    	   o_inst_sh,
    	   o_inst_sw,
    	   o_inst_addi,
    	   o_inst_slti,
    	   o_inst_sltiu,
    	   o_inst_xori,
    	   o_inst_ori,
    	   o_inst_andi,
    	   o_inst_slli,
    	   o_inst_srli,
    	   o_inst_srai, 
    	   o_inst_add,
    	   o_inst_sub,
    	   o_inst_sll,
    	   o_inst_slt,
    	   o_inst_sltu,
    	   o_inst_xor,
    	   o_inst_srl,
    	   o_inst_sra,
    	   o_inst_or,
    	   o_inst_and,
    	   o_inst_fence,
    	   o_inst_fence_i,
    	   o_inst_ecall,
    	   o_inst_ebreak,
    	   o_inst_csrrw,
    	   o_inst_csrrs,
    	   o_inst_csrrc,
    	   o_inst_csrrwi,
    	   o_inst_csrrsi,
    	   o_inst_csrrci
	   });
endmodule

