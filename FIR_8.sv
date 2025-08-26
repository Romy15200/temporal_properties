module Fir3Tap (
  input logic clk,
  input rst,
  input logic [3:0] x,
  output logic [7:0] y
);

  logic [7:0] h[2:0] = '{8'h1, 8'h2, 8'h1}; // 1 2 1
  logic [3:0] delay1, delay2;

  assign y = h[2]*x + h[1] * delay1 + h[0] * delay2;
  
  always_ff @(posedge clk or posedge rst) begin
    if (rst) begin
      delay1 <= 0;
      delay2 <= 0;
    end
    else begin
      delay1 <= x;
      delay2 <= delay1;
    end
  end
 

 ///////////     PROPERTIES   ///////////

property prop;
    @(posedge clk) disable iff (rst) ($stable(x) [*3] |-> y == x * 4);    
endproperty
 

property lemma;
@(posedge clk) disable iff (rst) ( $stable(x) [*3] |-> (delay2 == x && delay1 == x));
endproperty


property check_implies;
  @(posedge clk) disable iff (rst) ((delay1 == x && delay2 == x) implies y == 4 * x);
endproperty




// assume with --buechi --k-induction
/*
assert property(prop);
assume property(lemma);      // error: there is no property suitable for k-induction
*/


// Implication checks, might be irrelevant 
//assert property (lemma implies prop); //PROVEN as expected
// assert property (check_implies); //INCONCLUSIVE,  shouldn't it be logically valid with the circuit definitions?


//assert property(lemma and prop); //conversion error
//assert property(lemma && prop); //error: there is no property suitable for k-induction




endmodule


