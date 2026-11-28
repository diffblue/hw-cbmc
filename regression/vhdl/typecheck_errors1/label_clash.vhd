entity label_clash is
  port(clk : in bit; y : out bit);
end;
architecture rtl of label_clash is
  signal process1 : bit;
begin
  process1: process(clk)
  begin
    y <= '1';
  end process;
end;
