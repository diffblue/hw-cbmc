library ieee;
use ieee.std_logic_1164.all;

entity init_sl is
  port (clk : in std_logic; d : in std_logic);
end entity;

architecture rtl of init_sl is
  signal q : std_logic;  -- no initial value: 'U' in VHDL
  signal qv : std_logic_vector(1 downto 0);
begin
  process(clk)
  begin
    if rising_edge(clk) then
      q <= q;
      qv <= qv;
    end if;
  end process;
  -- in VHDL the initial value is 'U'; the model must not prove q = '0'
  p0: assert q = '0';
  p1: assert qv = "00";
end architecture;
