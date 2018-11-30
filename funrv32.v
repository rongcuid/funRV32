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
   reg syncing;
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
