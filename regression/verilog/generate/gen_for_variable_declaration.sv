module main;


generate 
    for (genvar i=0; i<2; i++) begin     // i cannot be defined in the loop header
        logic some_logic;
    end
endgenerate

endmodule


