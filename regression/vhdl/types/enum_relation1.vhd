-- IEEE 1076-2008 9.2.3: the ordering of enumeration values is the
-- order of the literals
entity enum_relation1 is
  port(y, z : out boolean);
end;
architecture rtl of enum_relation1 is
  type state_t is (idle, run, stop);
  signal s : state_t := run;
begin
  y <= s > idle;
  z <= s >= stop;
  p1: assert y;
  p2: assert not z;
  p3: assert idle < run and run < stop;
end;
