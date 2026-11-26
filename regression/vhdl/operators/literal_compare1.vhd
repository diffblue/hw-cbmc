-- IEEE 1076-2008 9.2.3: a string literal operand of a relational
-- operator takes the type of the other operand, but keeps its own
-- length; arrays of different length compare lexicographically
entity literal_compare1 is
  port(y : out boolean);
end;
architecture rtl of literal_compare1 is
  signal v : bit_vector(3 downto 0) := "1010";
begin
  y <= v /= "10";
  p1: assert v >= "1010";
  p2: assert not ("1010" > v);
  p3: assert v /= "10";
  p4: assert not (v = "10");
  p5: assert "11" > v;
  p6: assert v < "11";
  p7: assert y;
end;
