library ieee;
use ieee.std_logic_1164.all;
entity slv_integer is
  port(y : out std_logic_vector(7 downto 0));
end;
architecture rtl of slv_integer is
begin
  y <= 5;
end;
