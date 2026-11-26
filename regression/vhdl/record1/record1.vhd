-- A record type with element selection.

library ieee;
use ieee.std_logic_1164.all;

entity record1 is
  port(
    clk   : in  std_logic;
    valid : in  std_logic;
    data  : in  std_logic_vector(3 downto 0);
    q     : out std_logic_vector(3 downto 0));
end record1;

architecture rtl of record1 is

  type pkt_t is record
    valid : std_logic;
    data  : std_logic_vector(3 downto 0);
  end record;

  signal pkt : pkt_t := (valid => '0', data => "0000");

begin

  process(clk)
  begin
    if rising_edge(clk) then
      pkt.valid <= valid;
      if valid = '1' then
        pkt.data <= data;
      end if;
    end if;
  end process;

  q <= pkt.data;

  -- data only changes with valid
  p1: assert pkt.valid = '1' or pkt.data = "0000";
  p2: assert pkt.data = "0000";

end rtl;
