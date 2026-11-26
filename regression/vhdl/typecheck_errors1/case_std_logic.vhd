library ieee;
use ieee.std_logic_1164.all;
entity case_std_logic is
  port(a : in std_logic; y : out bit);
end;
architecture rtl of case_std_logic is
begin
  process(a)
  begin
    case a is
      when '0' => y <= '0';
      when '1' => y <= '1';
    end case;
  end process;
end;
