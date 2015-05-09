module top(clock, reset, line1, line2, outp, overflw);

  input clock;
  input reset;
  input line1;
  input line2;

  output outp;
  output overflw;

  reg outp;
  reg overflw;

  `define STATE0 3'b000
  `define STATE1 3'b001
  `define STATE2 3'b010
  `define STATE3 3'b011
  `define STATE4 3'b100
  `define STATE5 3'b101
  `define STATE6 3'b110
  `define STATE7 3'b111

  reg [2:0] stato;

  always @(posedge clock)
  begin
    if(reset == 1'b1)
    begin
      stato = `STATE0;
      outp = 1'b0;
      overflw = 1'b0;
    end
    else
    begin
      case (stato)
        `STATE0:
          begin
            if((line1 == 1'b1) && (line2 == 1'b1))
              stato = `STATE4;
            else
              stato = `STATE1;
            outp = line1 ^ line2;
            overflw = 1'b0;
          end

        `STATE3:
          begin
            if((line1 == 1'b1) && (line2 == 1'b1))
              stato = `STATE4;
            else
              stato = `STATE1;
            outp = line1 ^ line2;
            overflw = 1'b1;
          end

        `STATE1:
          begin
            if((line1 == 1'b1) && (line2 == 1'b1))
              stato = `STATE5;
            else
              stato = `STATE2;
            outp = line1 ^ line2;
            overflw = 1'b0;
          end

        `STATE4:
          begin
            if((line1 == 1'b1) && (line2 == 1'b1))
              stato = `STATE5;
            else
              stato = `STATE2;
            outp = ~(line1 ^ line2);
            overflw = 1'b0;
          end

        `STATE2:
          begin
            if((line1 == 1'b1) && (line2 == 1'b1))
              stato = `STATE7;
            else
              stato = `STATE6;
            outp = line1 ^ line2;
            overflw = 1'b0;
          end

        `STATE5:
          begin
            if((line1 == 1'b1) && (line2 == 1'b1))
              stato = `STATE7;
            else
              stato = `STATE6;
            outp = ~(line1 ^ line2);
            overflw = 1'b0;
          end

        `STATE6:
          begin
            if((line1 == 1'b1) && (line2 == 1'b1))
              stato = `STATE3;
            else
              stato = `STATE0;
            outp = line1 ^ line2;
            overflw = 1'b0;
          end

        `STATE7:
          begin
            if((line1 == 1'b1) && (line2 == 1'b1))
              stato = `STATE3;
            else
              stato = `STATE0;
            outp = ~(line1 ^ line2);
            overflw = 1'b0;
          end

      endcase
    end
  end

endmodule
