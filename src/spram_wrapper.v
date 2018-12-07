module spram_wrapper
  (
   input wire 	      clk,
   input wire [13:0]  addr,
   input wire [31:0]  wdata,
   input wire 	      wen,
   input wire [3:0]   ben,
   output wire [31:0] rdata
   );

   SB_SPRAM256KA spram0
     (
      .ADDRESS(addr),
      .DATAIN(wdata[15:0]),
      .MASKWREN({ben[1],ben[1],ben[0],ben[0]}),
      .WREN(wen),
      .CHIPSELECT(1'b1),
      .CLOCK(clk),
      .STANDBY(1'b0),
      .SLEEP(1'b0),
      .POWEROFF(1'b0),
      .DATAOUT(rdata[15:0]),
      );

   SB_SPRAM256KA spram1
     (
      .ADDRESS(addr),
      .DATAIN(wdata[31:16]),
      .MASKWREN({ben[3],ben[3],ben[2],ben[2]}),
      .WREN(wen),
      .CHIPSELECT(1'b1),
      .CLOCK(clk),
      .STANDBY(1'b0),
      .SLEEP(1'b0),
      .POWEROFF(1'b0),
      .DATAOUT(rdata[31:16]),
      );
   
endmodule // spram_wrapper

