module main;

  initial begin
    int i;
    for(i = 0; i < 10; i++) begin
      if(i == 5)
        break;
    end
    loop_exit: assert(i==5);
  end

endmodule
