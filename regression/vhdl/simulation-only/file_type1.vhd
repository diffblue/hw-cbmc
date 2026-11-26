library ieee;
use ieee.std_logic_1164.all;
entity file_type1 is port(clk, a : in std_logic); end;
architecture rtl of file_type1 is
  type ft is file of integer;
  file f : ft;
begin
end;
