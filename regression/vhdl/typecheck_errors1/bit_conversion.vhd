library ieee;
use ieee.std_logic_1164.all;
entity bit_conversion is
  port(a : in std_logic; y : out bit);
end;
architecture rtl of bit_conversion is
begin
  y <= bit(a);
end;
