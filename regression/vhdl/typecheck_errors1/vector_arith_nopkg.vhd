library ieee;
use ieee.std_logic_1164.all;
entity vector_arith_nopkg is
  port(a, b : in std_logic_vector(3 downto 0); y : out std_logic_vector(3 downto 0));
end;
architecture rtl of vector_arith_nopkg is
begin
  y <= a + b;
end;
