-- FSM with an enumeration type for the state.

library ieee;
use ieee.std_logic_1164.all;

entity enum_fsm1 is
  port(
    clk   : in  std_logic;
    reset : in  std_logic;
    start : in  std_logic;
    busy  : out std_logic);
end enum_fsm1;

architecture rtl of enum_fsm1 is

  type state_t is (idle, running, done);

  signal state    : state_t := idle;
  signal busy_int : std_logic;

begin

  process(clk, reset)
  begin
    if reset = '1' then
      state <= idle;
    elsif rising_edge(clk) then
      case state is
        when idle =>
          if start = '1' then
            state <= running;
          end if;
        when running =>
          state <= done;
        when done =>
          state <= idle;
      end case;
    end if;
  end process;

  busy_int <= '1' when state = running else '0';
  busy <= busy_int;

  -- busy tracks the running state
  p1: assert busy_int = '1' or state /= running;

  -- done is reachable
  p2: assert state /= done;

end rtl;
