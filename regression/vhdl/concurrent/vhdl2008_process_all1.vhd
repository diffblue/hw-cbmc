-- VHDL-2008: process(all) for combinational logic, and a conditional
-- signal assignment inside a process.

library ieee;
use ieee.std_logic_1164.all;

entity vhdl2008_process_all1 is
  port(
    a : in  std_logic;
    b : in  std_logic;
    s : in  std_logic;
    y : out std_logic);
end vhdl2008_process_all1;

architecture rtl of vhdl2008_process_all1 is

  signal y_int : std_logic;

begin

  process(all)
  begin
    y_int <= a when s = '1' else b;
  end process;

  y <= y_int;

  p1: assert y_int = a or y_int = b;
  p2: assert y_int = a;

end rtl;
