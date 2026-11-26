library ieee;
use ieee.std_logic_1164.all;
use std.textio.all;
entity file_decl1 is port(clk, a : in std_logic); end;
architecture rtl of file_decl1 is
  file f : text is "x";
begin
end;
