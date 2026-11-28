library ieee;
use ieee.std_logic_1164.all;

entity two_edges is
  port (clk : in std_logic; d : in std_logic);
end entity;

architecture rtl of two_edges is
  signal q_r : std_logic := '0';
  signal q_f : std_logic := '0';
begin
  -- rising-edge and falling-edge flops on the same clock; they
  -- sample d half a cycle apart and in general differ
  process(clk) begin
    if rising_edge(clk) then q_r <= d; end if;
  end process;
  process(clk) begin
    if falling_edge(clk) then q_f <= d; end if;
  end process;
  -- not true in VHDL; the model has one clock, and rejects this
  p0: assert q_r = q_f;
end architecture;
