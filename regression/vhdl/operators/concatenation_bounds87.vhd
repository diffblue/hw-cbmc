-- IEEE 1076-1987 7.2.3: the direction and left bound of a concatenation
-- are those of the left operand, unless that is a null array or an
-- element; VHDL-93 and later take them from the index subtype (see
-- concatenation_bounds1.vhd)
entity concatenation_bounds87 is
  port(y : out bit);
end;
architecture rtl of concatenation_bounds87 is
  constant a : bit_vector(7 downto 4) := "1100";
  constant b : bit_vector(3 downto 0) := "0001";
  constant c : bit_vector := a & b;
  constant d : bit_vector := '1' & b;
  constant e : bit_vector(0 to 1) := "10";
  constant f : bit_vector := e & a;
begin
  y <= c(7);
  p1: assert c'left = 7;
  p2: assert c'right = 0;
  p3: assert c(7) = '1' and c(6) = '1' and c(5) = '0' and c(0) = '1';
  p4: assert (a & b) = "11000001";
  p5: assert d'left = 0 and d'right = 4;
  p6: assert f'left = 0 and f'right = 5;
  p7: assert y = '1';
end;
