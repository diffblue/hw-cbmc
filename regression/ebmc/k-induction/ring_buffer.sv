module ring_buffer(input clk, input read, input write);

  reg [4:0] count=0;
  reg [3:0] readptr=0, writeptr=0;

  always @(posedge clk) begin
    if(read) begin
      readptr++;
      count--;
    end

    if(write) begin
      writeptr++;
      count++;
    end

  end

  wire full=count==16;
  wire empty=count==0;

  assume property (empty |-> !read);
  assume property (full |-> !write);

  p0: assert property (((writeptr-readptr)&'b1111)==count[3:0]);
  p1: assert property (count <= 16);
  p2: assert property (count != 17);

endmodule
