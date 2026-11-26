-- Simulation-only constructs, which the parser accepts and the type
-- checker rejects. The design is not meaningful.

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std."+";

package sim_pkg is
  type int_ptr is access integer;
  type int_file is file of integer;
  type wired is array (natural range <>) of std_logic;
  function resolve(s : wired) return std_logic;
  subtype rstd is resolve std_logic;
  subtype rint is resolve std_logic range '0' to '1';
  group pin_pair is (signal, signal);
  group g1 : pin_pair(a, b);
end package;

entity simulation1 is
  port(clk : in std_logic; a, b : in std_logic; y : out std_logic);
end entity;

architecture rtl of simulation1 is
  signal s, t : std_logic;
  signal v : std_logic_vector(1 to 3);
  file f : text open read_mode is "input.txt";
  file g : text is in "input.txt";
  type matrix is array (1 to 3, 1 to 3) of bit;
  disconnect s : std_logic after 5 ns;
begin

  b1: block (clk = '1') is
    generic(n : integer := 1);
    generic map(n => 2);
    port(p : in std_logic);
    port map(p => a);
    signal inner : std_logic;
  begin
    inner <= p;
  end block b1;

  s <= a after 1 ns, b after 2 ns, '0' after 3.5 ns;
  t <= "and"(a, b);
  (s, t) <= v(1 to 2);

  process
    variable ptr : int_ptr;
    variable k : integer;
  begin
    ptr := new integer;
    (k, k) := (1, 2);
    wait;
  end process;

  y <= s;
end architecture;

configuration cfg of simulation1 is
  use work.sim_pkg.all;
  for rtl
    for b1
    end for;
    for all : comp use entity work.comp(rtl);
    end for;
  end for;
end configuration cfg;
