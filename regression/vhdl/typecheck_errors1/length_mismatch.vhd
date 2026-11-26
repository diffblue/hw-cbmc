library ieee;
use ieee.std_logic_1164.all;
entity length_mismatch is
  port(a : in std_logic_vector(3 downto 0); y : out std_logic_vector(7 downto 0));
end;
architecture rtl of length_mismatch is
begin
  y <= a;
end;
