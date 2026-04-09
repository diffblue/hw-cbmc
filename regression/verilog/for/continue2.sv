module main(input index);

  // declare an array to verify that the correct index got skipped
  logic [10:0] array;

  initial begin : blk
    int i, j;
    j = 0;
    array = '0;
    for(i = 10; i >= 0; i--) begin
      if(i == 5)
        continue;
      j++;
      array[i] = 1'b1;
    end
    p0: assert(j==10);
    p1: assert(index == 5 -> array[index] == 0);
    p2: assert(index !=5 -> array[index] == 1);
  end

endmodule
