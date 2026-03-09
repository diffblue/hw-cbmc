module main;

  bit [10:0] some_data, other_data;

  always_comb begin
    for (int i = 0; i < 10; i++)
      some_data[i] = i%2;

    // a for with variable declaration comes with a scope,
    // so the below is not a redeclaration
    for (int i = 0; i < 10; i++)
      other_data[i] = !(i%2);
  end

endmodule
