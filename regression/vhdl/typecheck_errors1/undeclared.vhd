entity undeclared is
  port(a : in bit; b : out bit);
end undeclared;

architecture rtl of undeclared is
begin
  b <= c;
end rtl;
