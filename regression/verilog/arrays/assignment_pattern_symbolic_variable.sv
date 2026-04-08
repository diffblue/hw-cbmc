module main(
    // declare symbolic index to cover range of complete array
    input logic [1:0] symbolic_index);


    bit array1[3];
    bit [2:0] array2;
    bit [0:2] array3;
    bit [2:0] array4;


    assume property (symbolic_index >= 0);
    assume property (symbolic_index <= 2);

    // to test if tool can catch a bug by inserting a 0 in different positions of the array
    assign array1 = '{ 1, 1, 0 };
    p1: assert property (array1[symbolic_index] == 1);

    assign array2 = '{ 1, 0, 1 };
    p2: assert property (array2[symbolic_index] == 1);

    assign array3 = '{ 0, 1, 1 };
    p3: assert property (array3[symbolic_index] == 1);

    // this should be proven
    assign array4 = '{ 1, 1, 1 };
    p4: assert property (array4[symbolic_index] == 1);
endmodule
