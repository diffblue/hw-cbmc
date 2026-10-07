module main(input [63:0] rdata, input [7:0] w [0:7], output logic ok);

  // Does every w[i] match a distinct byte of rdata?
  // Each iteration reads back 'found' and 'used', and conditionally
  // updates them. This must not blow up RTL construction
  // (https://github.com/diffblue/hw-cbmc/issues/2196).
  logic [7:0] used;
  logic found;

  always_comb begin
    used = '0;
    ok = 1'b1;
    for (int i = 0; i < 8; i++) begin
      found = 1'b0;
      for (int j = 0; j < 8; j++)
        if (!found && !used[j] && w[i] == rdata[j*8 +: 8]) begin
          used[j] = 1'b1;
          found = 1'b1;
        end
      ok = ok && found;
    end
  end

  // the identity permutation matches
  p0: assert final (
    w[0]==rdata[7:0] && w[1]==rdata[15:8] && w[2]==rdata[23:16] &&
    w[3]==rdata[31:24] && w[4]==rdata[39:32] && w[5]==rdata[47:40] &&
    w[6]==rdata[55:48] && w[7]==rdata[63:56] -> ok);

  // the reverse permutation matches
  p1: assert final (
    w[7]==rdata[7:0] && w[6]==rdata[15:8] && w[5]==rdata[23:16] &&
    w[4]==rdata[31:24] && w[3]==rdata[39:32] && w[2]==rdata[47:40] &&
    w[1]==rdata[55:48] && w[0]==rdata[63:56] -> ok);

  // a match uses all bytes
  p2: assert final (ok -> used == 8'b11111111);

  // a match does not imply a particular order
  p3: assert final (ok -> w[0]==rdata[7:0]);

endmodule
