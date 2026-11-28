library ieee;
use ieee.std_logic_1164.all;
entity concat_mismatch is
  port(a : in bit_vector(3 downto 0); b : in std_logic; y : out std_logic_vector(4 downto 0));
end;
architecture rtl of concat_mismatch is
begin
  y <= a & b;
end;
