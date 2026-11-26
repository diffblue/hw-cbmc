-- Reset behaviour: two counters, one with a synchronous and one with an
-- asynchronous reset, each with the reset tied to a constant. With the
-- reset active the counters must stay at zero; with it inactive they
-- must count. An omitted or inverted reset branch fails one of these.

library ieee;
use ieee.std_logic_1164.all;

entity reset1 is
  port(
    clk : in std_logic);
end reset1;

architecture rtl of reset1 is

  signal rst_on  : std_logic := '1';
  signal rst_off : std_logic := '0';

  signal sync_held  : integer range 0 to 3 := 0;
  signal sync_free  : integer range 0 to 3 := 0;
  signal async_held : integer range 0 to 3 := 0;
  signal async_free : integer range 0 to 3 := 0;

begin

  rst_on  <= '1';
  rst_off <= '0';

  sync_a: process(clk)
  begin
    if rising_edge(clk) then
      if rst_on = '1' then
        sync_held <= 0;
      elsif sync_held /= 3 then
        sync_held <= sync_held + 1;
      end if;
    end if;
  end process;

  sync_b: process(clk)
  begin
    if rising_edge(clk) then
      if rst_off = '1' then
        sync_free <= 0;
      elsif sync_free /= 3 then
        sync_free <= sync_free + 1;
      end if;
    end if;
  end process;

  async_a: process(clk, rst_on)
  begin
    if rst_on = '1' then
      async_held <= 0;
    elsif rising_edge(clk) then
      if async_held /= 3 then
        async_held <= async_held + 1;
      end if;
    end if;
  end process;

  async_b: process(clk, rst_off)
  begin
    if rst_off = '1' then
      async_free <= 0;
    elsif rising_edge(clk) then
      if async_free /= 3 then
        async_free <= async_free + 1;
      end if;
    end if;
  end process;

  -- held in reset
  p1: assert sync_held = 0;
  p2: assert async_held = 0;

  -- counting
  p3: assert sync_free /= 2;
  p4: assert async_free /= 2;

end rtl;
