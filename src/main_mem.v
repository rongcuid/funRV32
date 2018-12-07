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

   reg [31:0]  im_rdata_p;
   reg [31:0]  dm_rdata_p;
   always @ (posedge i_clk) begin : MEM_OUT
      im_rdata_p <= im_rdata;
      dm_rdata_p <= dm_rdata;
   end

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
   assign o_im_rdata = im_rdata_p;
   assign o_dm_rdata = dm_rdata_p;

   //assume property (!(i_fence_i && i_dm_wen));
   // assert property ( @(posedge i_clk)i_fence_i |=> !o_ready );
   // assert property (@(posedge i_clk)i_fence_i |=> syncing);
   // assert property (@(posedge i_clk)syncing & clean_end |=> clean_head == 8'b0);
   // assert property (@(posedge i_clk)syncing & clean_end |=> dirty_head == 8'b0);
   
endmodule

