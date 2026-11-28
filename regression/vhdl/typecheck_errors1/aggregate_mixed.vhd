entity aggregate_mixed is
  port(y : out bit_vector(3 downto 0));
end;
architecture rtl of aggregate_mixed is
begin
  y <= ('1', 2 => '0', '1', '0');
end;
