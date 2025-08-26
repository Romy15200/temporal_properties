//https://circuitcove.com/design-examples-memory/

module SinglePortMemoryByteEn #(parameter MEM_SIZE=16, parameter LOG_MEM_SIZE=4)(
  input  logic                 clk,
  input  logic                 writeEn,
  input  logic [  4-1:0]       byteEn,
  input logic  [LOG_MEM_SIZE-1:0] readAddr,
  input  logic [LOG_MEM_SIZE-1:0] writeAddr,
  input  logic [32-1:0] writeData,
  output logic [32-1:0] readData
);

  logic [32-1:0] mem[MEM_SIZE];

  always_ff @(posedge clk) begin
  if (writeEn) begin
    if (byteEn[0]) begin
      mem[writeAddr][7:0] <= writeData[7:0];
    end
    if (byteEn[1]) begin
      mem[writeAddr][15:8] <= writeData[15:8];
    end
    if (byteEn[2]) begin
      mem[writeAddr][23:16] <= writeData[23:16];
    end
    if (byteEn[3]) begin
      mem[writeAddr][31:24] <= writeData[31:24];
    end
  end
end


  assign readData = mem[readAddr];
  
  property prop;
      @(posedge clk) (byteEn == 0 and writeEn) |=> (mem == $past(mem));
  endproperty


  assert property(prop); // Invariant check failed, File: arith_tools.cpp:181 function: from_integer, core dumped
endmodule

