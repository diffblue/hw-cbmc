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

  wire full=count==15;
  wire empty=count==0;

  assume property (empty |-> !read);
  assume property (full |-> !write);

  assert property (((writeptr-readptr)&'b1111)==count);

endmodule

