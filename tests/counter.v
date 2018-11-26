module counter
(
  input wire clk,
  input wire resetb,
  input wire en,
  input wire we,
  input wire [31:0] cmp_din,
  output wire cmp
);
  reg [31:0] mtimecmp, mtime;

  always @ (posedge clk) begin : COUNTER_PIPELINE
    if (!resetb) begin
      mtime <= 32'b0;
      mtimecmp <= 32'bX;
    end
    else if (clk) begin
      if (en) begin
        mtime <= mtime + 32'b1;
      end
      if (we) begin
        mtimecmp <= cmp_din;
      end
    end
  end

  assign cmp = mtime == mtimecmp;
endmodule

module counter_top
(
  input wire clk,
  input wire resetb,
  output reg led
);
  reg en, we;
  wire cmp;

  counter C0(.clk(clk),.resetb(resetb),
    .en(en),.we(we),.cmp_din(32'h1000),.cmp(cmp));

  reg cmp_written;
  always @ (posedge clk) begin
    if (!resetb) begin
      led <= 1'b0;
      cmp_written <= 1'b0;
      we <= 1'b0;
      en <= 1'b0;
    end
    else if (clk) begin
      cmp_written <= 1'b1;
      en <= 1'b1;
      we <= !cmp_written;
      led <= cmp ? ~led : led;
    end
  end
endmodule
