-- IEEE 1076-2008 16.2.2: O'subtype denotes the subtype of an object
entity subtype_attribute1 is
  port(i : in integer range 0 to 15; s : out integer range 0 to 15);
end;
architecture rtl of subtype_attribute1 is
  signal t : i'subtype;
begin
  t <= i;
  s <= 0 when i > s'subtype'right else t;
end;
