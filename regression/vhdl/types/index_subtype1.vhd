-- IEEE 1076-2008 9.3.2: a string literal of an unconstrained array type
-- gets the left bound and direction of the index subtype of the type;
-- for bit_vector the index subtype is natural, here it is positive
entity index_subtype1 is
  port(y : out bit);
end;
architecture rtl of index_subtype1 is
  type pvec is array (positive range <>) of bit;
  constant c : pvec := "10";
  constant d : bit_vector := "10";
  subtype down is integer range 5 downto 0;
  type dvec is array (down range <>) of bit;
  constant e : dvec := "100";
begin
  y <= c(1);
  p1: assert c'left = 1;
  p2: assert c'right = 2;
  p3: assert c(1) = '1';
  p4: assert c(2) = '0';
  p5: assert d'left = 0;
  p6: assert d'right = 1;
  p7: assert e'left = 5;
  p8: assert e'right = 3;
  p9: assert e(5) = '1' and e(4) = '0' and e(3) = '0';
  p10: assert y = '1';
end;
