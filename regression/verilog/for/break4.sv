module main(input [31:0] bits);

  int index;

  always_comb begin
    // linear decrementing loop to find the most significant bit that is 1
    for(index = $bits(bits)-1; index >= 0; index--)
      if(bits[index])
        break;

     p0: assert final(bits == 'b1 -> index == 0);
     p3: assert final(bits == 'b1000 -> index == 3);
     p4: assert final(bits == 'b11110 -> index == 4);

  end

endmodule
