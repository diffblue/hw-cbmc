module main(input [31:0] bits);

  var [5:0] index;

  always_comb @bits begin
    // linear loop to find the first bit that is 1
    int i;
    for(i = 0; i < $bits(bits); i++)
      if(bits[i])
        break;

     index = i;
     assert final(bits == 'b1 -> index == 0);
     assert final(bits == 'b1000 -> index == 3);
     assert final(bits == 0 -> index == 32);
  end

endmodule
