-- Syntax coverage for the parser; the design is not meaningful.

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;

package parse1_pkg is
  constant WIDTH : positive := 16#10#;
  constant PERIOD : time := 10 ns;
  constant RATIO : real := 1.5e3;
  constant BIG : integer := 1_000_000;
  constant EXP : integer := 2E3;
  type color_t is (red, green, blue);
  type word_array_t is array (natural range <>) of std_logic_vector(7 downto 0);
  subtype nibble_t is std_logic_vector(3 downto 0);
  type pair_t is record
    first  : integer range 0 to 255;
    second : std_logic_vector(1 downto 0);
  end record;
  function "and" (a, b : color_t) return color_t;
  function max(a, b : integer) return integer;
  procedure swap(variable a, b : inout integer);
  attribute keep : boolean;
  alias byte_t is std_logic_vector;
end package parse1_pkg;

package body parse1_pkg is
  function "and" (a, b : color_t) return color_t is
  begin
    return a;
  end function "and";

  function max(a, b : integer) return integer is
  begin
    if a > b then
      return a;
    else
      return b;
    end if;
  end function;

  procedure swap(variable a, b : inout integer) is
    variable t : integer;
  begin
    t := a;
    a := b;
    b := t;
  end procedure swap;
end package body parse1_pkg;

library ieee;
use ieee.std_logic_1164.all;
use work.parse1_pkg.all;

entity parse1 is
  generic(
    N : positive := 8;
    constant INIT : std_logic_vector := x"A5");
  port(
    clk, rst : in  std_logic;
    d        : in  std_logic_vector(N-1 downto 0);
    io       : inout std_logic;
    b        : buffer std_logic;
    q        : out std_logic_vector(N-1 downto 0) := (others => '0'));
end entity parse1;

architecture rtl of parse1 is

  signal r      : std_logic_vector(N-1 downto 0) := (others => '0');
  signal p      : pair_t := (first => 0, second => "00");
  signal c      : color_t := red;
  signal \Extended Name\ : boolean;
  constant ZERO : nibble_t := (others => '0');
  shared variable sv : integer;

  component sub is
    generic(G : integer := 1);
    port(i : in std_logic; o : out std_logic);
  end component sub;

  for all : sub use entity work.sub(rtl);

  attribute keep of r : signal is true;

  function lsb(v : std_logic_vector) return std_logic is
  begin
    return v(v'right);
  end;

begin

  u0: sub generic map(G => 2) port map(i => clk, o => open);
  u1: sub port map(clk, b);
  u2: entity work.sub(rtl) port map(i => clk, o => io);

  g0: for i in r'range generate
    q(i) <= r(i) and d(i);
  end generate g0;

  g1: if N > 4 generate
    \Extended Name\ <= true;
  end generate;

  seq: process(clk, rst) is
    variable v : unsigned(N-1 downto 0);
    variable count : natural range 0 to 3 := 0;
  begin
    if rst = '1' then
      r <= (others => '0');
    elsif rising_edge(clk) then
      v := unsigned(d) + to_unsigned(1, N);
      r <= std_logic_vector(v);
      p.first <= p.first + 1;
      p.second(0) <= d(0);
      for i in 0 to N-1 loop
        next when i = 2;
        exit when i = 6;
        r(i) <= d(N-1-i);
      end loop;
      l1: while count < 3 loop
        count := count + 1;
      end loop l1;
      case c is
        when red | green => c <= blue;
        when others => c <= red;
      end case;
      case p.first is
        when 0 to 10 => null;
        when 11 => null;
        when others => null;
      end case;
      assert v /= 0 report "wrapped" severity note;
      report "cycle" severity note;
      swap(sv, sv);
      with d(1 downto 0) select
        b <= '1' when "00",
             '0' when others;
      io <= std_logic'('Z');
    end if;
  end process seq;

  comb: process(all)
  begin
    q(0) <= lsb(r) when c = red else '0';
  end process;

  tb: process
  begin
    wait until rising_edge(clk);
    wait on clk, rst;
    wait for 10 ns;
    wait;
  end process;

  a0: assert r /= d report "equal" severity warning;
  postponed assert b = '0' or b = '1';

end architecture rtl;
