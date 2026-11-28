entity power_nonstatic is
  port(a : in integer; y : out integer);
end;
architecture rtl of power_nonstatic is
begin
  y <= a ** 2;
end;
