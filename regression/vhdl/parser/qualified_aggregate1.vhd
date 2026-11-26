entity qualified_aggregate1 is end;
architecture a of qualified_aggregate1 is
  signal q : bit_vector(3 downto 0);
begin
  q <= bit_vector'(others => '0');
end;
