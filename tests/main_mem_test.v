module main_mem_top
   (
    input wire i_clk,
    input wire i_rst
    );

   reg 	       dm_ren, dm_wen, fence_i;
   reg [13:0]  dm_addr;
   wire [31:0] im_rdata, dm_rdata;
   reg [31:0]  dm_wdata;
   wire        ready;

   (*keep*)
   reg [31:0] result_i, result_d;
   
   main_mem mem0
     (
      .i_clk(i_clk), .i_rst(i_rst),
      .i_im_ren(1'b1), .i_im_addr(14'bX),
      .o_im_rdata(im_rdata),
      .i_dm_ren(dm_ren), .i_dm_wen(dm_wen),
      .i_dm_ben(4'b1), .i_dm_addr(dm_addr),
      .i_dm_wdata(dm_wdata), .o_dm_rdata(dm_rdata),
      .i_fence_i(fence_i), .o_ready(ready)
      );
   always @ (posedge i_clk) begin
      if (i_rst) begin
	 dm_addr <= 14'b0;
	 dm_wdata <= 32'b0;
	 dm_wen <= 1'b1;
	 fence_i <= 1'b0;
      end
      else begin
	 if (ready) begin
	    dm_addr <= dm_addr + 14'h1000;
	    dm_wdata <= dm_wdata + 32'h10000;
	 end
	 fence_i <= dm_addr[10];
      end
   end // always @ (posedge i_clk)
   always @ (posedge i_clk)
     result_i <= im_rdata;
   always @ (posedge i_clk)
     result_d <= dm_rdata;
endmodule
