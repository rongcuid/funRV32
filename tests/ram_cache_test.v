module ram_cache_top
  (
   input wire 	      clk,
   input wire 	      reset,
   );

   wire        mem_wen;
   wire [3:0]  mem_ben;
   wire [13:0] mem_addr;
   (*keep*)
   wire        im_miss, dm_miss;
   (*keep*)
   wire [31:0] im_rdata, dm_rdata;
   wire [31:0] mem_rdata, mem_wdata;

   (*keep*)
   reg [13:0]  im_addr, dm_addr;
   (*keep*)
   reg [31:0]  dm_wdata;

   (*keep*)
   reg [3:0]   dm_ben;

   ram_cache ccu0
     (
      .clk(clk), .reset(reset),
      .im_ren(1'b1), .im_addr(im_addr), .im_rdata(im_rdata), .im_miss(im_miss),
      .dm_ren(1'b1), .dm_addr(dm_addr), .dm_rdata(dm_rdata), .dm_miss(dm_miss),
      .dm_ben(dm_ben), .dm_wdata(dm_wdata),
      .mem_addr(mem_addr), .mem_wdata(mem_wdata), .mem_ben(mem_ben), .mem_wen(mem_wen),
      .mem_rdata(mem_rdata)
      );

   spram_wrapper ram0
     (
      .clk(clk), .addr(mem_addr), .wdata(mem_wdata),
      .wen(mem_wen), .ben(mem_ben), .rdata(mem_rdata)
      );
   
   always @ (posedge clk) begin
      if (reset) begin
	 im_addr <= 14'b0;
	 dm_addr <= 14'b0;
	 dm_wdata <= 32'hFFFFFFFF;
	 dm_ben <= 4'b0;
      end
      else if (clk) begin
	 im_addr <= im_addr + 14'b1;
	 dm_addr <= dm_addr + 14'b1;
	 dm_wdata <= dm_wdata - 32'b1;
	 dm_ben <= dm_addr[2] ? 4'b1111 : 4'b0000;
      end
   end
endmodule
