-- A for-generate statement building a ripple of registers.

library ieee;
use ieee.std_logic_1164.all;

entity generate1 is
  port(
    clk : in  std_logic;
    din : in  std_logic;
    dout : out std_logic);
end generate1;

architecture rtl of generate1 is

  constant N : natural := 4;

  signal stage : std_logic_vector(N downto 0) := (others => '0');

begin

  stage(0) <= din;

  gen: for i in 1 to N generate
    process(clk)
    begin
      if rising_edge(clk) then
        stage(i) <= stage(i-1);
      end if;
    end process;
  end generate;

  dout <= stage(N);

  -- the last stage is the first stage delayed by N cycles,
  -- so it is still at its initial value for N-1 cycles
  p1: assert stage(N) = '0';

  -- but earlier stages have changed by then
  p2: assert stage(2) = '0';

end rtl;
