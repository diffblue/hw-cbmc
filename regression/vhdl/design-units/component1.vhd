-- Hierarchy: a component declaration, two instances with named
-- port association, and a property over the sub-instance outputs.

library ieee;
use ieee.std_logic_1164.all;

entity toggle is
  port(
    clk : in  std_logic;
    en  : in  std_logic;
    q   : out std_logic);
end toggle;

architecture rtl of toggle is
  signal q_int : std_logic := '0';
begin
  process(clk)
  begin
    if rising_edge(clk) then
      if en = '1' then
        q_int <= not q_int;
      end if;
    end if;
  end process;
  q <= q_int;
end rtl;

library ieee;
use ieee.std_logic_1164.all;

entity component1 is
  port(
    clk : in  std_logic;
    en  : in  std_logic;
    q0  : out std_logic;
    q1  : out std_logic);
end component1;

architecture rtl of component1 is

  component toggle
    port(
      clk : in  std_logic;
      en  : in  std_logic;
      q   : out std_logic);
  end component;

  signal t0, t1 : std_logic;

begin

  u0: toggle port map(clk => clk, en => en, q => t0);
  u1: toggle port map(clk => clk, en => en, q => t1);

  q0 <= t0;
  q1 <= t1;

  -- both instances see the same enable, so they stay in lockstep
  p1: assert t0 = t1;

  -- and they do toggle
  p2: assert t0 = '0';

end rtl;
