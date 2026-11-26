entity index_range1 is end;
architecture a of index_range1 is
  signal v : bit_vector(1 downto 0);
begin
  v(2) <= '1';
end;
