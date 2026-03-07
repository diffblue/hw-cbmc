module main(input [31:0] bits);

  var [5:0] index;

  always_comb @bits begin
    // linear loop to find the first bit that is 1
    for(index = 0; index < $bits(bits); index++)
      if(bits[index])
        break;

    p0: assert final(bits == 'b1 -> index == 0);
    p3: assert final(bits == 'b1000 -> index == 3);
    p32: assert final(bits == 0 -> index == 32);
  end

endmodule
