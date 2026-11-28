-- IEEE 1076-2008 15.6: a character literal is written with quotes,
-- and is distinct from an identifier with the same letter
entity character_literal1 is
  port(clk : in bit; y : out bit);
end;
architecture rtl of character_literal1 is
  type tri_t is ('0', '1', 'Z');
  signal z : tri_t := 'Z';
begin
  process(clk)
  begin
    if clk = '1' then
      if z = 'Z' then
        z <= '0';
      else
        z <= 'Z';
      end if;
    end if;
  end process;
  y <= '1' when z = 'Z' else '0';
  p1: assert z = 'Z' or z = '0';
  p2: assert (y = '1') = (z = 'Z');
end;
