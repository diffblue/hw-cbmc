-- IEEE 1076-2008 6.4.2.2: a constant of an unconstrained array type
-- takes its index range from the value
entity unconstrained_constant1 is
  port(y : out bit_vector(3 downto 0));
end;
architecture rtl of unconstrained_constant1 is
  constant c : bit_vector := "0101";
begin
  y <= c;
  p1: assert c'length = 4;
  p2: assert y = "0101";
end;
