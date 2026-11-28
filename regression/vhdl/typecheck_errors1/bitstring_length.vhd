library ieee;
use ieee.std_logic_1164.all;
entity bitstring_length is
  port(y : out std_logic_vector(7 downto 0));
end;
architecture rtl of bitstring_length is
begin
  y <= x"F";
end;
