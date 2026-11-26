entity exponent_huge is
  port(y : out integer);
end;
architecture rtl of exponent_huge is
begin
  y <= 1E999999999;
end;
