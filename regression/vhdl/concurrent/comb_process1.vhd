-- A combinational process (sensitivity list without a clock) next to a
-- clocked one. The combinational process computes the next state.

library ieee;
use ieee.std_logic_1164.all;

entity comb_process1 is
  port(
    clk  : in  std_logic;
    up   : in  std_logic;
    cnt  : out integer range 0 to 3);
end comb_process1;

architecture rtl of comb_process1 is

  signal state      : integer range 0 to 3 := 0;
  signal next_state : integer range 0 to 3;

begin

  comb: process(state, up)
  begin
    if up = '1' then
      if state = 3 then
        next_state <= 0;
      else
        next_state <= state + 1;
      end if;
    else
      next_state <= state;
    end if;
  end process;

  seq: process(clk)
  begin
    if clk'event and clk = '1' then
      state <= next_state;
    end if;
  end process;

  cnt <= state;

  p1: assert next_state <= 3;
  p2: assert state /= 2;

end rtl;
