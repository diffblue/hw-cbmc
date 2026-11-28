entity logical_length is
  port(a : in bit_vector(3 downto 0); b : in bit_vector(1 downto 0); y : out bit_vector(3 downto 0));
end;
architecture rtl of logical_length is
begin
  y <= a and b;
end;
