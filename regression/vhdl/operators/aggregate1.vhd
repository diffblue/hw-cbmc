-- IEEE 1076-2008 9.3.3.3: positional and named array aggregates
entity aggregate1 is
  port(y, z : out bit_vector(3 downto 0); w : out bit_vector(0 to 3));
end;
architecture rtl of aggregate1 is
begin
  y <= ('1', '0', others => '1');
  z <= (3 => '1', 1 downto 0 => '0', others => '1');
  w <= ('1', '0', '0', '0');
  p1: assert y = "1011";
  p2: assert z = "1100";
  p3: assert w = "1000";
end;
