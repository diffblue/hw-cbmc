-- IEEE 1076-2008 5.3.2.2: a null array has no elements; to_integer of
-- a null vector is 0 in numeric_std. Null arrays have no bit-vector
-- counterpart and are rejected rather than mapped to a zero-width
-- bit-vector.
library ieee;
use ieee.numeric_std.all;
entity null_array1 is
end;
architecture rtl of null_array1 is
  signal v : integer := to_integer(signed'(""));
begin
end;
