library ieee;
use ieee.std_logic_1164.all;

entity agg_to is
  port (clk : in std_logic);
end entity;

architecture rtl of agg_to is
  signal v : std_logic_vector(0 to 3);
  signal w : std_logic_vector(0 to 3);
begin
  v <= ('1', '0', '0', '0');  -- v(0) = '1'
  w <= (0 => '1', others => '0'); -- w(0) = '1'
  -- expected: both PROVED
  p0: assert v(0) = '1';
  p1: assert v(3) = '0';
  p2: assert w(0) = '1';
  p3: assert v = "1000";
end architecture;
