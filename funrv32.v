/*
 * This register file does not support internal forwarding.
 * It also returns invalid on x0
 */
module regfile
  (
   input wire 	     clk,
   input wire 	     we,
   input wire [4:0]  a1,
   input wire [4:0]  ad,
   output reg [31:0] r1,
   input wire [31:0] rd
   );

   reg [31:0] 	     data [0:31] /*verilator public*/;
   integer 	     i;
   always @ (posedge clk) begin
      if (we) data[~ad] <= rd;
      r1 <= data[~a1];
   end
endmodule // regfile

module decoder
  (
   input wire [31:0]  inst,
   output wire [31:0] immediate,
   output wire [4:0]  a_rs1,
   output wire [4:0]  a_rs2,
   output wire [4:0]  a_rd,
   output wire 	      inst_lui,
   output wire 	      inst_auipc,
   output wire 	      inst_jal,
   output wire 	      inst_jalr,
   output wire 	      inst_beq,
   output wire 	      inst_bne,
   output wire 	      inst_blt,
   output wire 	      inst_bge,
   output wire 	      inst_bltu,
   output wire 	      inst_bgeu,
   output wire 	      inst_lb,
   output wire 	      inst_lh,
   output wire 	      inst_lw,
   output wire 	      inst_lbu,
   output wire 	      inst_lhu,
   output wire 	      inst_sb,
   output wire 	      inst_sh,
   output wire 	      inst_sw,
   output wire 	      inst_addi,
   output wire 	      inst_slti,
   output wire 	      inst_sltiu,
   output wire 	      inst_xori,
   output wire 	      inst_ori,
   output wire 	      inst_andi,
   output wire 	      inst_slli,
   output wire 	      inst_srli,
   output wire 	      inst_srai, 
   output wire 	      inst_add,
   output wire 	      inst_sub,
   output wire 	      inst_sll,
   output wire 	      inst_slt,
   output wire 	      inst_sltu,
   output wire 	      inst_xor,
   output wire 	      inst_srl,
   output wire 	      inst_sra,
   output wire 	      inst_or,
   output wire 	      inst_and,
   output wire 	      inst_fence,
   output wire 	      inst_fence_i,
   output wire 	      inst_ecall,
   output wire 	      inst_ebreak,
   output wire 	      inst_csrrw,
   output wire 	      inst_csrrs,
   output wire 	      inst_csrrc,
   output wire 	      inst_csrrwi,
   output wire 	      inst_csrrsi,
   output wire 	      inst_csrrci
   );

endmodule

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
