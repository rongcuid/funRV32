module funrv32_reg_top
  (
   input wire clk, 
   input wire reset,
   output wire eq1,
   output wire eq2
   );

   reg [4:0]  a1, a2, ad;
   wire [31:0] rs1, rs2;
   reg [31:0]  rd;
   (*keep*)
   reg [31:0]  d_rs1, d_rs2;

   regfile
     rf0 (.clk(clk), .we(1'b1),.a1(a1), .a2(a2),.ad(ad),.r1(rs1),.r2(rs2),.rd(rd));

   always @ (posedge clk) begin
      if (reset) begin
	 a1 <= 5'b0;
	 a2 <= 5'b0;
	 ad <= 5'b0;
	 rd <= 32'b0;
      end
      else if (clk) begin
	 a1 <= a1 + 5'b1;
	 a2 <= a2 + 5'b1;
	 ad <= ad + 5'b1;
	 rd <= rd + 32'b1;
      end
   end // always @ (posedge clk)

   always @ (posedge clk) begin
      d_rs1 <= rs1;
      d_rs2 <= rs2;
   end
endmodule
