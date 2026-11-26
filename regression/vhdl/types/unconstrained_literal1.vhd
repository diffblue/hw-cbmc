-- IEEE 1076-2008 9.3.2: the index range of a string literal is
-- determined by the context; for an unconstrained array type it is
-- ascending and starts at the left bound of the index subtype
entity unconstrained_literal1 is
  port(y : out bit);
end;
architecture rtl of unconstrained_literal1 is
  constant c : bit_vector := "0001";
begin
  y <= c(3);
  p1: assert c'left = 0;
  p2: assert c'right = 3;
  p3: assert c'length = 4;
  p4: assert c(0) = '0';
  p5: assert c(3) = '1';
  p6: assert y = '1';
end;
