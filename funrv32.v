/*
 These are encoded as {funct7[5], funct3}
 */
`define ALUOP_ADD       4'b0000
//`define ALUOP_SUB 	4'b1000
`define ALUOP_SLL       4'b0001
`define ALUOP_SLT 	4'b0010
`define ALUOP_SLTU 	4'b0011
`define ALUOP_XOR	4'b0100
`define ALUOP_SRL       4'b0101
`define ALUOP_SRA       4'b1101
`define ALUOP_OR	4'b0110
`define ALUOP_AND       4'b0111

/*
 * This register file does not support internal forwarding.
 * It also returns invalid on x0
 */
module regfile
  (
   input wire 	      clk,
   input wire 	      we,
   input wire [4:0]   a1,
   input wire [4:0]   a2,
   input wire [4:0]   ad,
   output wire [31:0] r1,
   output wire [31:0] r2,
   input wire [31:0]  rd
   );

   reg [31:0] 	      data [0:31] /*verilator public*/;
   integer 	      i;
   reg [31:0] 	      r1_tmp;
   reg [31:0] 	      r2_tmp;
   always @ (posedge clk) begin
      if (we) data[~ad] <= rd;
      r1_tmp <= data[~a1];
      r2_tmp <= data[~a2];
   end

   wire forward_1, forward_2;
   assign forward_1 = a1 == ad;
   assign forward_2 = a2 == ad;
   reg 	forward_1_p, forward_2_p;
   reg [31:0] rd_p;
   always @ (posedge clk) begin
      forward_1_p <= forward_1;
      forward_2_p <= forward_2;
      rd_p <= rd;
   end
   assign r1 = forward_1 ? rd
	       : forward_1_p ? rd_p
	       : r1_tmp;
   assign r2 = forward_2 ? rd
	       : forward_2_p ? rd_p
	       : r2_tmp;
   
endmodule // regfile

`ifdef NONE
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
   wire 	      cat_load, cat_store, cat_branch, cat_jalr, cat_miscmem,
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
      case (inst[6:2])
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
     = imm_i ? { {21{inst[31]}}, inst[30:20] }
       : imm_s ? { {21{inst[31]}}, inst[30:25], inst[11:7] }
       : imm_b ? { {20{inst[31]}}, inst[7], inst[30:25], inst[11:8], 1'b0 }
       : imm_u ? { inst[31:12], 12'b0 }
       : imm_j ? { {12{inst[31]}}, inst[19:12], inst[20], inst[30:21], 1'b0 }
       : 32'bX;

   wire [2:0] funct3;
   assign funct3 = inst[14:12];
   assign funct7 = inst[31:25];


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
    	   o_inst_csrrci,
    	   o_inst_illegal
	   });
endmodule
`endif
module spram_wrapper
  (
   input wire 	      clk,
   input wire [13:0]  addr,
   input wire [31:0]  wdata,
   input wire 	      wen,
   input wire [3:0]   ben,
   output wire [31:0] rdata
   );

   SB_SPRAM256KA spram0
     (
      .ADDRESS(addr),
      .DATAIN(wdata[15:0]),
      .MASKWREN({ben[1],ben[1],ben[0],ben[0]}),
      .WREN(wen),
      .CHIPSELECT(1'b1),
      .CLOCK(clk),
      .STANDBY(1'b0),
      .SLEEP(1'b0),
      .POWEROFF(1'b0),
      .DATAOUT(rdata[15:0]),
      );

   SB_SPRAM256KA spram1
     (
      .ADDRESS(addr),
      .DATAIN(wdata[31:16]),
      .MASKWREN({ben[3],ben[3],ben[2],ben[2]}),
      .WREN(wen),
      .CHIPSELECT(1'b1),
      .CLOCK(clk),
      .STANDBY(1'b0),
      .SLEEP(1'b0),
      .POWEROFF(1'b0),
      .DATAOUT(rdata[31:16]),
      );
   
endmodule // spram_wrapper

module main_mem
  (
   input wire 	      i_clk,
   input wire 	      i_rst,
  
   input wire 	      i_im_ren,
   input wire [13:0]  i_im_addr,
   output wire [31:0] o_im_rdata,
  
   input wire 	      i_dm_ren,
   input wire 	      i_dm_wen,
   input wire [3:0]   i_dm_ben,
   input wire [13:0]  i_dm_addr,
   input wire [31:0]  i_dm_wdata,
   output wire [31:0] o_dm_rdata,

   input wire 	      i_fence_i,
   output wire 	      o_ready
   );

   reg [13:0] 	      dirty [0:255];
   reg [7:0] 	      dirty_head, clean_head;
   wire 	      do_write;
   reg 		      dirty_addr;
   wire 	      dirty_full;

   assign dirty_full = &dirty_head;
   assign do_write = !dirty_full && i_dm_wen;

   // Keep track of all DM writes
   always @ (posedge i_clk) begin : DIRTY_INDEX
      if (do_write) begin
	 dirty[dirty_head] <= i_dm_addr;
      end
      dirty_addr <= dirty[clean_head];
   end

   wire next_sync;
   assign next_sync = i_fence_i || dirty_full; // This wastes one clock on dirty_full
   reg 	syncing;
   wire do_sync;
   assign do_sync = next_sync || syncing;
   
   wire [13:0] im_addr, dm_addr;
   wire [31:0] im_rdata, im_wdata, dm_rdata, dm_wdata;
   wire        im_wen, dm_wen;
   wire [3:0]  dm_ben;
   spram_wrapper spram0
     (.clk(i_clk), .addr(im_addr), .wdata(im_wdata), .wen(im_wen),
      .ben(4'b1111), .rdata(im_rdata));
   spram_wrapper spram1
     (.clk(i_clk), .addr(dm_addr), .wdata(dm_wdata), .wen(dm_wen),
      .ben(dm_ben), .rdata(dm_rdata)
      );

   reg 	       do_sync_p, do_sync_pp;
   reg [13:0]  dirty_addr_p, dirty_addr_pp;
   always @ (posedge i_clk) begin : MEM_PIPELINE
      if (i_rst) begin
	 do_sync_p <= 1'b0;
	 do_sync_pp <= 1'b0;
      end
      else begin
	 do_sync_p <= do_sync;
	 do_sync_pp <= do_sync_p;
	 dirty_addr_p <= dirty_addr;
	 dirty_addr_pp <= dirty_addr_p;
      end
   end

   assign im_wen = do_sync_pp;
   assign im_addr = do_sync_pp ? dirty_addr_pp : i_im_addr;
   assign im_wdata = dm_rdata;
   
   assign dm_wen = do_sync_p ? 1'b1 : i_dm_wen;
   assign dm_ben = do_sync_p ? 4'b1111 : i_dm_ben;
   assign dm_addr = do_sync_p ? dirty_addr_p : i_dm_addr;
   assign dm_wdata = i_dm_wdata;

   wire clean_end;
   assign clean_end = clean_head == dirty_head;
   always @ (posedge i_clk) begin : MEM_FSM
      if (i_rst) begin
	 dirty_head <= 8'b0;
	 syncing <= 1'b0;
	 clean_head <= 8'b0;
      end
      else begin
	 clean_head <= 8'b0;
	 if (do_write) begin
	    dirty_head <= dirty_head + 8'b1;
	 end
	 if (do_sync) begin
	    syncing <= !clean_end;
	    clean_head <= clean_end ? 8'b0 : clean_head + 8'b1;
	    dirty_head <= clean_end ? 8'b0 : dirty_head;
	 end
      end
   end

   assign o_ready = !dirty_full && !do_sync_p && !do_sync_pp;
   assign o_im_rdata = im_rdata;
   assign o_dm_rdata = dm_rdata;

   //assume property (!(i_fence_i && i_dm_wen));
   // assert property ( @(posedge i_clk)i_fence_i |=> !o_ready );
   // assert property (@(posedge i_clk)i_fence_i |=> syncing);
   // assert property (@(posedge i_clk)syncing & clean_end |=> clean_head == 8'b0);
   // assert property (@(posedge i_clk)syncing & clean_end |=> dirty_head == 8'b0);
   
endmodule

module main_alu
  (
   input wire i_clk,
   input wire [31:0] i_op1,
   input wire [31:0] i_op2,
   input wire [3:0]  i_opsel,
   output reg [31:0] o_aluout
   );

   reg [31:0] 	      add_p, sub_p, sll_p, xor_p, srl_p, sra_p, or_p, and_p;
   reg [3:0] 	      opsel_p, opsel;
   // Split into a signed comparison on high and unsigned on low
   reg 		      sltl_p, slth_p, sltuh_p;
   reg 		      slth, sltl, sltuh;

   reg [31:0] 	      op1, op2;
   //reg [15:0] 	      op1_sll16, op1_srl16;
   //reg [15:0] 	      sll16_p, srl16_p;
   //reg 		      s16sel;
   reg 		      s16sel_p;

   wire [31:0] 	      adder_out;
   assign adder_out = op1 + op2;
   always @ (posedge i_clk) begin
      op1 <= i_op1;
      op2 <= i_op2;
      // s16sel <= i_op2[4];
      //op1_sll16 <= i_op1[15:0];
      //op1_srl16 <= i_op1[31:16];
      opsel <= i_opsel;
      slth <= $signed(i_op1[16+:16]) < $signed(i_op2[16+:16]);
      sltuh <= i_op1[16+:16] < i_op2[16+:16];
      sltl <= i_op1[0+:16] < i_op2[0+:16];
      
      add_p <= adder_out;
      
      sll_p <= op1 << op2[3:0];
      srl_p <= op1 >> op2[3:0];
      sra_p <= op1 >>> op2[3:0];
      s16sel_p <= op2[4];
      
      xor_p <= op1 ^ op2;
      or_p <= op1 | op2;
      and_p <= op1 & op2;
      slth_p <= slth;
      sltuh_p <= sltuh;
      sltl_p <= sltl;
      // slth_p <= $signed(op1[16+:16]) < $signed(op2[16+:16]);
      // sltuh_p <= op1[16+:16] < op2[16+:16];
      // sltl_p <= op1[0+:16] < op2[0+:16];
      opsel_p <= opsel;
   end
   
   always @ (*) begin : ALU_LOGIC
      case (opsel_p)
	`ALUOP_ADD: o_aluout = add_p;
	`ALUOP_SLL: o_aluout = s16sel_p ? {sll_p[0+:16],16'b0} : sll_p;
	`ALUOP_SLT: o_aluout = {31'b0, (slth_p ? 1'b1 : sltl_p)};
	`ALUOP_SLTU: o_aluout = {31'b0, (sltuh_p ? 1'b1 : sltl_p)};
	`ALUOP_XOR: o_aluout = xor_p;
	`ALUOP_SRL: o_aluout = s16sel_p ? {16'b0, srl_p[16+:16]} : srl_p;
	`ALUOP_SRA: o_aluout = s16sel_p ? {{16{sra_p[31]}}, sra_p[16+:16]} : sra_p;
	`ALUOP_OR: o_aluout = or_p;
	`ALUOP_AND: o_aluout = and_p;
	default: o_aluout = 32'bX;
      endcase // case (i_opsel)
   end
endmodule // main_alu
