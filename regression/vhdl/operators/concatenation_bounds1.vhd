-- IEEE 1076-2008 9.2.5: the direction of a concatenation is that of
-- the index subtype S of the base type, and its left bound is S'left,
-- regardless of the bounds of the operands (VHDL-87 took them from the
-- left operand); if both operands are null arrays, the result is the
-- right operand
entity concatenation_bounds1 is
  port(y : out bit);
end;
architecture rtl of concatenation_bounds1 is
  constant a : bit_vector(7 downto 4) := "1100";
  constant b : bit_vector(3 downto 0) := "0001";
  constant c : bit_vector := a & b;
  type pvec is array (positive range <>) of bit;
  constant p : pvec := pvec'("1") & pvec'("0");
begin
  y <= c(7);
  p1: assert c'left = 0;
  p2: assert c'right = 7;
  p3: assert c(0) = '1' and c(1) = '1' and c(2) = '0' and c(7) = '1';
  p4: assert (a & b) = "11000001";
  p5: assert p'left = 1 and p'right = 2;
  p6: assert p(1) = '1' and p(2) = '0';
  p7: assert y = '1';
end;
