`include "aluop.vh"
module main_alu
  (
   input wire 	     i_clk,
   input wire [31:0] i_op1,
   input wire [31:0] i_op2,
   input wire [3:0]  i_opsel,
   output reg [31:0] o_aluout
   );

//`ifdef FAST_MAC
   reg [31:0] 	     op1_add_p;
   reg [31:0] 	     op2_add_p;
   reg [31:0] 	     op1_sub_p;
   reg [31:0] 	     op2_sub_p;
   reg [31:0] 	     op1_sll_p;
   reg [4:0] 	     op2_sll_p;
   reg [31:0] 	     op1_slt_p;
   reg [31:0] 	     op2_slt_p;
   reg [31:0] 	     op1_sltu_p;
   reg [31:0] 	     op2_sltu_p;
   reg [31:0] 	     op1_xor_p;
   reg [31:0] 	     op2_xor_p;
   reg [31:0] 	     op1_srl_p;
   reg [4:0] 	     op2_srl_p;
   reg [31:0] 	     op1_sra_p;
   reg [4:0] 	     op2_sra_p;
   reg [31:0] 	     op1_or_p;
   reg [31:0] 	     op2_or_p;
   reg [31:0] 	     op1_and_p;
   reg [31:0] 	     op2_and_p;

   wire [31:0] 	     add_tmp;
   reg [31:0] 	     add_pp ;
   wire [31:0] 	     sub_tmp;
   wire 	     sub_co;
   reg [31:0] 	     sub_pp ;
   reg [31:0] 	     sll_pp ;
   reg 		     slt_pp;

   reg 		     sltuh_pp, sltul_pp;
   reg 		     sll16sel_pp, srl16sel_pp, sra16sel_pp;
   
   reg [31:0] 	     xor_pp ;
   reg [31:0] 	     srl_pp ;
   reg [31:0] 	     sra_pp ;
   reg [31:0] 	     or_pp ;
   reg [31:0] 	     and_pp ;

   reg [3:0] 	     opsel_p, opsel_pp;

   SB_MAC16
     #(
       .TOPADDSUB_UPPERINPUT(1'b1), // C
       .TOPADDSUB_CARRYSELECT(2'b11), // Borrow bottom
       .BOTADDSUB_UPPERINPUT(1'b1) // B
       ) sub0 (
      .CLK(i_clk), .CE(1'b1),
      .C(op1_sub_p[31:16]), .A(op2_sub_p[31:16]),
      .B(op1_sub_p[15:0]), .D(op2_sub_p[15:0]),
      .AHOLD(1'b0), .BHOLD(1'b0), .CHOLD(1'b0), .DHOLD(1'b0),
      .IRSTTOP(1'b0), .IRSTBOT(1'b0), .ORSTTOP(1'b0), .ORSTBOT(1'b0),
      .OLOADTOP(1'b0), .OLOADBOT(1'b0), .ADDSUBTOP(1'b1), .ADDSUBBOT(1'b1),
      .OHOLDTOP(1'b0), .OHOLDBOT(1'b0), 
      .CI(), .ACCUMCI(), .SIGNEXTIN(), .SIGNEXTOUT(), .CO(sub_co), .ACCUMCO(),
      .O(sub_tmp)
      );

   SB_MAC16
     #(
       .TOPADDSUB_UPPERINPUT(1'b1), // C
       .TOPADDSUB_CARRYSELECT(2'b11), // Borrow bottom
       .BOTADDSUB_UPPERINPUT(1'b1) // B
       ) add0 (
      .CLK(i_clk), .CE(1'b1),
      .C(op1_add_p[31:16]), .A(op2_add_p[31:16]),
      .B(op1_add_p[15:0]), .D(op2_add_p[15:0]),
      .AHOLD(1'b0), .BHOLD(1'b0), .CHOLD(1'b0), .DHOLD(1'b0),
      .IRSTTOP(1'b0), .IRSTBOT(1'b0), .ORSTTOP(1'b0), .ORSTBOT(1'b0),
      .OLOADTOP(1'b0), .OLOADBOT(1'b0), .ADDSUBTOP(1'b0), .ADDSUBBOT(1'b0),
      .OHOLDTOP(1'b0), .OHOLDBOT(1'b0), 
      .CI(), .ACCUMCI(), .SIGNEXTIN(), .SIGNEXTOUT(), .CO(), .ACCUMCO(),
      .O(add_tmp)
      );
   
   always @ (posedge i_clk) begin : ALU_PIPELINE
      opsel_p <= i_opsel;
      op1_add_p <= i_op1;
      op2_add_p <= i_op2;
      op1_sub_p <= i_op1;
      op2_sub_p <= i_op2;
      op1_sll_p <= i_op1;
      op2_sll_p <= i_op2[4:0];
      op1_slt_p <= i_op1;
      op2_slt_p <= i_op2;
      op1_sltu_p <= i_op1;
      op2_sltu_p <= i_op2;
      op1_xor_p <= i_op1;
      op2_xor_p <= i_op2;
      op1_srl_p <= i_op1;
      op2_srl_p <= i_op2[4:0];
      op1_sra_p <= i_op1;
      op2_sra_p <= i_op2[4:0];
      op1_or_p <= i_op1;
      op2_or_p <= i_op2;
      op1_and_p <= i_op1;
      op2_and_p <= i_op2;

      opsel_pp <= opsel_p;
      add_pp <= add_tmp;

      sub_pp <= sub_tmp;

      sll_pp <= op1_sll_p << op2_sll_p[3:0];
      sll16sel_pp <= op2_sll_p[4];
      slt_pp <= sub_co;
      sltuh_pp <= op1_sltu_p[16+:16] < op2_sltu_p[16+:16];
      sltul_pp <= op1_sltu_p[0+:16] < op2_sltu_p[0+:16];
      xor_pp <= op1_xor_p ^ op2_xor_p;
      srl_pp <= op1_srl_p >> op2_srl_p[3:0];
      srl16sel_pp <= op2_srl_p[4];
      sra_pp <= op1_sra_p >>> op2_sra_p[3:0];
      sra16sel_pp <= op2_sra_p[4];
      or_pp <= op1_or_p | op2_or_p;
      and_pp <= op1_and_p & op2_and_p;
   end // block: ALU_PIPELINE
   
   always @ (*) begin : ALU_LOGIC
      case (opsel_pp)
	`ALUOP_ADD: o_aluout = add_pp;
	`ALUOP_SUB: o_aluout = sub_pp;
	`ALUOP_SLL: o_aluout = sll16sel_pp ? {sll_pp[0+:16],16'b0} : sll_pp;
	`ALUOP_SLT: o_aluout = {31'b0, slt_pp};
	`ALUOP_SLTU: o_aluout = {31'b0, (sltuh_pp ? 1'b1 : sltul_pp)};
	`ALUOP_XOR: o_aluout = xor_pp;
	`ALUOP_SRL: o_aluout = srl16sel_pp ? {16'b0, srl_pp[16+:16]} : srl_pp;
	`ALUOP_SRA: o_aluout = sra16sel_pp ? {{16{sra_pp[31]}}, sra_pp[16+:16]} : sra_pp;
	`ALUOP_OR: o_aluout = or_pp;
	`ALUOP_AND: o_aluout = and_pp;
	default: o_aluout = 32'bX;
      endcase // case (i_opsel)
   end // block: ALU_LOGIC
//`endif
   
`ifdef FAST
   reg [31:0] 	     op1_add_p;
   reg [31:0] 	     op2_add_p;
   reg [31:0] 	     op1_sub_p;
   reg [31:0] 	     op2_sub_p;
   reg [31:0] 	     op1_sll_p;
   reg [4:0] 	     op2_sll_p;
   reg [31:0] 	     op1_slt_p;
   reg [31:0] 	     op2_slt_p;
   reg [31:0] 	     op1_sltu_p;
   reg [31:0] 	     op2_sltu_p;
   reg [31:0] 	     op1_xor_p;
   reg [31:0] 	     op2_xor_p;
   reg [31:0] 	     op1_srl_p;
   reg [4:0] 	     op2_srl_p;
   reg [31:0] 	     op1_sra_p;
   reg [4:0] 	     op2_sra_p;
   reg [31:0] 	     op1_or_p;
   reg [31:0] 	     op2_or_p;
   reg [31:0] 	     op1_and_p;
   reg [31:0] 	     op2_and_p;
   
   reg [31:0] 	     add_pp ;
   reg [31:0] 	     sub_pp ;
   reg [31:0] 	     sll_pp ;
   reg 		     slth_pp, sltl_pp;
   reg 		     sltuh_pp, sltul_pp;
   reg 		     sll16sel_pp, srl16sel_pp, sra16sel_pp;
   
   reg [31:0] 	     xor_pp ;
   reg [31:0] 	     srl_pp ;
   reg [31:0] 	     sra_pp ;
   reg [31:0] 	     or_pp ;
   reg [31:0] 	     and_pp ;

   reg [3:0] 	     opsel_p, opsel_pp;

   always @ (posedge i_clk) begin : ALU_PIPELINE
      opsel_p <= i_opsel;
      op1_add_p <= i_op1;
      op2_add_p <= i_op2;
      op1_sub_p <= i_op1;
      op2_sub_p <= ~i_op2;
      op1_sll_p <= i_op1;
      op2_sll_p <= i_op2[4:0];
      op1_slt_p <= i_op1;
      op2_slt_p <= i_op2;
      op1_sltu_p <= i_op1;
      op2_sltu_p <= i_op2;
      op1_xor_p <= i_op1;
      op2_xor_p <= i_op2;
      op1_srl_p <= i_op1;
      op2_srl_p <= i_op2[4:0];
      op1_sra_p <= i_op1;
      op2_sra_p <= i_op2[4:0];
      op1_or_p <= i_op1;
      op2_or_p <= i_op2;
      op1_and_p <= i_op1;
      op2_and_p <= i_op2;

      opsel_pp <= opsel_p;
      add_pp <= op1_add_p + op2_add_p;

      sub_pp <= op1_sub_p + op2_sub_p + 32'b1;

      sll_pp <= op1_sll_p << op2_sll_p[3:0];
      sll16sel_pp <= op2_sll_p[4];
      slth_pp <= $signed(op1_slt_p[16+:16]) < $signed(op1_slt_p[16+:16]);
      sltl_pp <= op1_slt_p[0+:16] < op2_slt_p[0+:16];
      sltuh_pp <= op1_sltu_p[16+:16] < op2_sltu_p[16+:16];
      sltul_pp <= op1_sltu_p[0+:16] < op2_sltu_p[0+:16];
      xor_pp <= op1_xor_p ^ op2_xor_p;
      srl_pp <= op1_srl_p >> op2_srl_p[3:0];
      srl16sel_pp <= op2_srl_p[4];
      sra_pp <= op1_sra_p >>> op2_sra_p[3:0];
      sra16sel_pp <= op2_sra_p[4];
      or_pp <= op1_or_p | op2_or_p;
      and_pp <= op1_and_p & op2_and_p;
   end // block: ALU_PIPELINE
   
   always @ (*) begin : ALU_LOGIC
      case (opsel_pp)
	`ALUOP_ADD: o_aluout = add_pp;
	`ALUOP_SUB: o_aluout = sub_pp;
	`ALUOP_SLL: o_aluout = sll16sel_pp ? {sll_pp[0+:16],16'b0} : sll_pp;
	`ALUOP_SLT: o_aluout = {31'b0, (slth_pp ? 1'b1 : sltl_pp)};
	`ALUOP_SLTU: o_aluout = {31'b0, (sltuh_pp ? 1'b1 : sltul_pp)};
	`ALUOP_XOR: o_aluout = xor_pp;
	`ALUOP_SRL: o_aluout = srl16sel_pp ? {16'b0, srl_pp[16+:16]} : srl_pp;
	`ALUOP_SRA: o_aluout = sra16sel_pp ? {{16{sra_pp[31]}}, sra_pp[16+:16]} : sra_pp;
	`ALUOP_OR: o_aluout = or_pp;
	`ALUOP_AND: o_aluout = and_pp;
	default: o_aluout = 32'bX;
      endcase // case (i_opsel)
   end // block: ALU_LOGIC

`endif //  `ifdef FAST
   
   
`ifdef MEDIUM
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
   end // block: ALU_LOGIC
`endif //  `ifdef MEDIUM
endmodule // main_alu
