-- IEEE 1076-2008 10.9: the choices cover each value exactly once
entity case_complete1 is
  port(a : in integer range 0 to 3; b : in bit_vector(1 downto 0); y, z : out bit);
end;
architecture rtl of case_complete1 is
  type state_t is (idle, run, stop);
  signal s : state_t := idle;
begin
  process(a, b, s)
  begin
    case a is
      when 0 | 1 => y <= '0';
      when 2 to 3 => y <= '1';
    end case;
    case b is
      when "00" | "01" => z <= '0';
      when "10" => z <= '1';
      when "11" => z <= '1';
    end case;
    case s is
      when idle => null;
      when run | stop => null;
    end case;
  end process;
  p1: assert (y = '1') = (a >= 2);
  p2: assert (z = '1') = (b(1) = '1');
end;
