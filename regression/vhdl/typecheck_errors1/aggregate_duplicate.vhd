entity aggregate_duplicate is
  port(y : out bit_vector(3 downto 0));
end;
architecture rtl of aggregate_duplicate is
begin
  y <= (0 => '1', 1 => '0', 0 => '1', others => '0');
end;
