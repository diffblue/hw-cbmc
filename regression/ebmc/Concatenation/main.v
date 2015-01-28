module main(x, y, z);

        input [7:0] y, z;
        output [9:0] x;
        reg [9:0] x;
        always @(y or z) begin
        x = { y[5:2], z[6:1] };  

        assert property1: (!(y == 12) && !(z == 2)) || (x != 0);
        end
endmodule
