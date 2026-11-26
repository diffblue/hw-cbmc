entity power_range is
  port(y : out integer);
end;
architecture rtl of power_range is
begin
  y <= 2**40;
end;
