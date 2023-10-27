module main();                                                                                                                                                                                                 
    supply0 ground;
    supply1 power;
    supply0 [3:0] ground_vec;
    supply1 [3:0] power_vec;

    always assert pground: ground == 0;
    always assert ppower: power == 1;
    always assert pground_vec: ground_vec == 'b0000;
    always assert ppower_vec: power_vec == 'b1111;

endmodule

