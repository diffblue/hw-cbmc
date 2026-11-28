-- IEEE 1076-2008 16.2.2: the attributes of scalar types
entity type_attributes1 is
  port(y : out integer; z : out boolean);
end;
architecture rtl of type_attributes1 is
  type state_t is (idle, run, stop);
  subtype small is integer range 2 to 5;
  signal s : state_t := state_t'left;
begin
  y <= integer'high;
  z <= s = idle and state_t'right = stop;
  p1: assert y = 2147483647;
  p2: assert z;
  p3: assert integer'low = -2147483648;
  p4: assert small'low = 2 and small'high = 5 and small'left = 2;
  p5: assert state_t'low = idle and state_t'high = stop;
end;
