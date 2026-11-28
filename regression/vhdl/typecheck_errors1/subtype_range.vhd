entity subtype_range is
  port(y : out integer);
end;
architecture rtl of subtype_range is
  subtype s is natural range -1 to 3;
begin
  y <= 0;
end;
