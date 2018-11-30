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

module ram_cache
  (
   input wire 	      clk,
   input wire 	      reset,
   input wire 	      im_ren,
   input wire [13:0]  im_addr,
   output wire [31:0] im_rdata,
   output wire 	      im_miss,

   input wire 	      dm_ren,
   input wire [3:0]   dm_ben,
   input wire [13:0]  dm_addr,
   input wire [31:0]  dm_wdata,
   output wire [31:0] dm_rdata,
   output wire 	      dm_miss,

   output wire 	      ready,

   output wire [13:0] mem_addr,
   output wire [31:0] mem_wdata,
   output wire [3:0]  mem_ben,
   output wire 	      mem_wen,
   input wire [31:0]  mem_rdata,

   );
   reg [15:0] 	      tags [0:255];
   reg [31:0] 	      cache [0:255];

   integer 	      i;
   initial begin
      for (i=0; i<256; i=i+1)
	tags[i] = 16'b0;
   end
   
   // 2R1W
   reg [15:0] tag_im, tag_dm;
   reg [31:0] data_im, data_dm;
   wire       cache_wen;
   wire [7:0] cache_waddr;
   wire [31:0] cache_wdata;
   wire [15:0] tag_wdata;
   always @ (posedge clk) begin : MEMORY
      if (im_ren) begin
	 tag_im <= tags[im_addr[7:0]];
	 data_im <= cache[im_addr[7:0]];
      end
      if (dm_ren) begin
	 tag_dm <= tags[dm_addr[7:0]];
	 data_dm <= cache[dm_addr[7:0]];
      end
      if (cache_wen) begin
	 tags[cache_waddr] <= tag_wdata;
	 cache[cache_waddr] <= cache_wdata;
      end
   end

   assign im_miss = (!tag_im[15]) || (im_tag_p != tag_im[5:0]);
   assign dm_miss = (!tag_dm[15]) || (dm_tag_p != tag_dm[5:0]);
   // Encoded so that next state is {0, im_miss, dm_miss} at HIT
   localparam
     HIT = 3'b000,
     MISS_IM = 3'b010,
     WAIT_IM = 3'b110,
     MISS_DM = 3'b001,
     WAIT_DM = 3'b101,
     MISS_BOTH = 3'b011,
     WAIT_BOTH = 3'b111;
   
   reg [2:0] ccu_state;
   /*
    The cache controller state machine. DM miss is handled before IM
    miss to commit part of pipeline
    @reset: start with MISS_IM
    @HIT: do nothing special
    @MISS_IM: retrieve instruction memory to cache
    @MISS_DM: retrieve data memory to cache
    @MISS_BOTH: retrieve data memory, then instruction memory
    */
   always @ (posedge clk) begin : CCU_FSM
      if (reset) begin
	 ccu_state <= MISS_IM;
      end
      else if (clk) begin
	 case (ccu_state)
	   HIT: begin
	      ccu_state <= {1'b0, im_miss, dm_miss};
	   end
	   MISS_IM: begin
	      ccu_state <= WAIT_IM;
	   end
	   WAIT_IM: begin
	      ccu_state <= HIT;
	   end
	   MISS_DM: begin
	      ccu_state <= WAIT_DM;
	   end
	   WAIT_DM: begin
	      ccu_state <= HIT;
	   end
	   MISS_BOTH: begin
	      ccu_state <= WAIT_BOTH;
	   end
	   WAIT_BOTH: begin
	      ccu_state <= WAIT_IM;
	   end
	   default: begin
	   end
	 endcase
      end
   end

   reg [5:0] im_tag_p, dm_tag_p;
   reg [7:0] im_index_p, dm_index_p;
   reg [3:0] dm_ben_p;
   reg 	     dm_store_p;
   always @ (posedge clk) begin : CCU_DPU
      case (ccu_state)
	HIT: begin
	   im_tag_p <= im_addr[13:8];
	   im_index_p <= im_addr[7:0];
	   dm_tag_p <= dm_addr[13:8];
	   dm_index_p <= dm_addr[7:0];
	   dm_ben_p <= dm_ben;
	   dm_store_p <= |dm_ben;
	end
	MISS_IM: begin
	end
	WAIT_IM: begin
	end
	MISS_DM: begin
	end
	WAIT_DM: begin
	end
	MISS_BOTH: begin
	end
	WAIT_BOTH: begin
	end
	default: begin
	end
      endcase
   end

   assign tag_wdata = (ccu_state == MISS_DM || ccu_state == MISS_BOTH)
     ? {2'b10, 8'bX, dm_tag_p} : {2'b10, 8'bX, im_tag_p};
   assign cache_waddr
     = (ccu_state == MISS_DM || ccu_state == MISS_BOTH)
       ? dm_index_p
       : im_index_p;
   assign cache_wen = ccu_state == WAIT_IM 
		      || ccu_state ==  WAIT_DM
		      || ccu_state == WAIT_BOTH;
   assign cache_wdata = dm_store_p ? dm_wdata : mem_rdata;
   assign mem_ben = dm_ben_p;
   assign mem_wen = ccu_state == MISS_DM && dm_store_p;
   assign mem_addr = (ccu_state == MISS_DM || ccu_state == MISS_BOTH)
     ? {dm_tag_p, dm_index_p} : {im_tag_p, im_index_p};
   assign mem_wdata = dm_wdata;
   assign im_rdata = data_im;
   assign dm_rdata = data_dm;
   assign ready = ccu_state == HIT;
endmodule // ram_cache
