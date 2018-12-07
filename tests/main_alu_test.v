module main_alu_top
  (
   input wire clk,
   input wire rst
   );
   wire       lock;
   wire       pll_clk;
    SB_PLL40_CORE #(
        .FEEDBACK_PATH("SIMPLE"),
        .PLLOUT_SELECT("GENCLK"),
        .DIVR(4'b0000),
        .DIVF(7'b0101111),
        .DIVQ(3'b100),
        .FILTER_RANGE(3'b001)
    ) pll0 (
        .LOCK(lock),
        .RESETB(1'b1),
        .BYPASS(1'b0),
        .REFERENCECLK(clk),
        .PLLOUTCORE(pll_clk)
    );
   reg [31:0] op1, op2;
   reg [3:0] opsel;
   wire [31:0] aluout;
   (*keep*)
   reg [31:0]  result;
   main_alu ALU0
     (
      .i_clk(pll_clk),
      .i_op1(op1), .i_op2(op2), .i_opsel(opsel),
      .o_aluout(aluout)
      );

   always @ (posedge pll_clk) begin
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
   always @ (posedge pll_clk) begin
	 result <= aluout;
   end
endmodule // main_alu_top
