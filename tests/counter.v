module counter
(
    input wire clk,
    input wire resetb,
    input wire wenl,
    input wire wenh,
    input wire sel,
    input wire [31:0] din,
    output wire cmp,
    output reg [31:0] mtimel,
    output reg [31:0] mtimeh,
    output reg [63:0] mtimecmp
);

wire [31:0] mtimeh1;
assign mtimeh1 = mtimeh + 32'b1;
always @ (posedge clk) begin : MTIME
    if (!resetb) begin
        mtimel <= 64'b0;
        mtimeh <= 64'b0;
    end
    else if (clk) begin
        mtime <= mtime + 32'b1;
        mtimeh <= &{mtime} ? mtimeh1 : mtimeh;
        if (wenl && !sel) begin
            mtimel <= din;
        end
        if (wenh && !sel) begin
            mtimeh <= din;
        end
    end
end

always @ (posedge clk) begin : MTIMECMP
    if (wenl && sel) mtimecmp[0+:32] <= din;
    if (wenh && sel) mtimecmp[32+:32] <= din;
end

  assign cmp = mtime == mtimecmp;
  endmodule

  module counter_top
  (
      input wire clk,
      input wire resetb,
      output reg led
  );
  (*keep*)
  reg we;
  (*keep*)
  wire cmp;
  (*keep*)
  wire [31:0] mtimel, mtimeh;
  (*keep*)
  wire [63:0] mtimecmp;
  counter C0(.clk(clk),.resetb(resetb),
      .wenl(we),.wenh(1'b0),.sel(1'b1),.din(32'h1000),.cmp(cmp),
      .mtimel(mtimel),.mtimeh(mtimeh),.mtimecmp(mtimecmp)
  );

  reg cmp_written;
  always @ (posedge clk) begin
      if (!resetb) begin
          led <= 1'b0;
          cmp_written <= 1'b0;
          we <= 1'b0;
      end
      else if (clk) begin
          cmp_written <= 1'b1;
          we <= !cmp_written;
          led <= cmp ? ~led : led;
      end
  end
  endmodule
