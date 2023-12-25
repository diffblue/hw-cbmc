// as 'description'
typedef bit my_type1;

module main();

  // as 'module_item'
  typedef bit my_type2;
  my_type2 my_type2_var;

  function some_function;
    // as 'block_item'
    typedef bit my_type3;
    begin
      my_type3 my_type3_var;
    end
  endfunction

  task some_task;
    // as 'block_item'
    typedef bit my_type4;
    begin
      my_type4 my_type4_var;
    end
  endtask

  always @my_type2_var begin : named_block
    typedef bit my_type5;
    my_type5 my_type5_var;
  end

endmodule
