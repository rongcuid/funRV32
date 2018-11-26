/*
 * This register file does not support internal forwarding.
 * It also returns invalid on x0
 */
module funrv32_reg
  (
   input wire 	     clk,
   input wire 	     we,
   input wire [4:0]  a1,
   input wire [4:0]  ad,
   output reg [31:0] r1,
   input wire [31:0] rd
   );

   reg [31:0] 	      data [0:31] /*verilator public*/;
   integer 	      i;
   always @ (posedge clk) begin
      if (we) data[~ad] <= rd;
      r1 <= data[~a1];
   end
endmodule

module funrv32_cached_ram
  (
   );
endmodule
