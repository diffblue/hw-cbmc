module main(input [31:0] bits);

  var [5:0] index;

  always_comb @bits begin
    // linear loop to find the first bit that is 1
    int i;
    for(i = 0; i < $bits(bits); i++)
      if(bits[i])
        break;

    index = i;
    p0: assert(bits == 'b1 -> index == 0);
    p3: assert(bits == 'b1000 -> index == 3);
    p4: assert(bits == 'b11000 -> index == 3);
    p32: assert(bits == 0 -> index == 32);
  end

endmodule
