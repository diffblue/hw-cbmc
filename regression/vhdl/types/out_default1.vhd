-- IEEE 1076-2008 6.4.2.3: an out port that is not driven has the
-- default value T'left
entity out_default1 is
  port(y : out integer range 3 to 7; z : out bit_vector(1 downto 0); w : out boolean);
end;
architecture rtl of out_default1 is
begin
  p1: assert y = 3;
  p2: assert z = "00";
  p3: assert not w;
end;
