module main_alu_top
  (
   input wire clk,
   input wire rst
   );
   reg [31:0] op1, op2;
   reg [3:0] opsel;
   wire [31:0] aluout;
   (*keep*)
   reg [31:0]  result;
   main_alu ALU0
     (
      .i_clk(clk),
      .i_op1(op1), .i_op2(op2), .i_opsel(opsel),
      .o_aluout(aluout)
      );

   always @ (posedge clk) begin
      if (rst) begin
	 op1 <= 32'b0;
	 op2 <= 32'hffffffff;
	 opsel <= 4'b0;
      end
      else begin
	 opsel <= opsel + 32'b1;
	 op1 <= op1 + 32'h10000;
	 op2 <= op2 + 32'h100000;
      end
   end // always @ (posedge clk)
   always @ (posedge clk) begin
	 result <= aluout;
   end
endmodule // main_alu_top
