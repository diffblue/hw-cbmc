-- IEEE 1076-2008 10.5.2.2: the value assigned to an array object keeps
-- its own index range; the elements correspond by position. The
-- lowering of a slice must use the slice's range, not the target's.
-- An earlier version retyped the value with the target's range and
-- extracted the wrong bits, so p1 was refuted.
entity slice_range1 is
  port(v : in bit_vector(0 to 7); h : out bit_vector(3 downto 0);
       d : in bit_vector(7 downto 0); e : out bit_vector(3 downto 0));
end;
architecture rtl of slice_range1 is
  constant c : bit_vector(0 to 3) := "1010";
  signal s : bit_vector(3 downto 0) := c;
begin
  h <= v(4 to 7);
  e <= d(7 downto 4)(7 downto 4);
  p1: assert h = v(4 to 7);
  p2: assert h(3) = v(4) and h(0) = v(7);
  p3: assert e = d(7 downto 4);
  p4: assert e(3) = d(7);
  p5: assert s = "1010" and s(3) = '1' and s(0) = '0';
end;
