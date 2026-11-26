library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
entity to_integer_slv is
  port(a : in std_logic_vector(3 downto 0); y : out integer);
end;
architecture rtl of to_integer_slv is
begin
  y <= to_integer(a);
end;
