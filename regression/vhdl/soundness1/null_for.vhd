library ieee;
use ieee.std_logic_1164.all;

entity null_for is
  port (clk : in std_logic);
end entity;

architecture rtl of null_for is
  signal v : std_logic_vector(3 downto 0) := "0000";
begin
  process(clk)
  begin
    if rising_edge(clk) then
      for i in 1 to 0 loop  -- null range: body must not execute
        v(i) <= '1';
      end loop;
    end if;
  end process;
  p0: assert v = "0000";
end architecture;
