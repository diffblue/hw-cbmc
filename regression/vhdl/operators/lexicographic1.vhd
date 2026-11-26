-- IEEE 1076-2008 9.2.3: the predefined relational operators on
-- arrays compare lexicographically
entity lexicographic1 is
  port(y : out boolean);
end;
architecture rtl of lexicographic1 is
  constant a : bit_vector := "100";
  constant b : bit_vector := "11";
begin
  y <= a < b;
  p1: assert y;
  p2: assert a /= b;
  p3: assert not (a = b);
  p4: assert "1" < "10" and "10" > "1" and "0" <= "00";
  p5: assert "11" > "10" and "10" >= "10";
end;
