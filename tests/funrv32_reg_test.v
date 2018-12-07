module funrv32_reg_top
  (
   input wire clk, 
   input wire resetb,
   output wire eq1,
   output wire eq2
   );

   (*keep*)
   reg [4:0]  a1, a2, ad;
   (*keep*)
   wire [31:0] rs1, rs2;
   (*keep*)
   reg [31:0]  rd;
   regfile
     rf0 (.clk(clk), .we(1'b1),.a1(a1), .a2(a2),.ad(ad),.r1(rs1),.r2(rs2),.rd(rd));
   always @ (posedge clk) begin
      if (!resetb) begin
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
   assign eq1 = rs1 == rd;
   assign eq2 = rs2 == rd;
   
   
endmodule
