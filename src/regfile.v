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
   assign forward_1 = we && a1 == ad;
   assign forward_2 = we && a2 == ad;
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

