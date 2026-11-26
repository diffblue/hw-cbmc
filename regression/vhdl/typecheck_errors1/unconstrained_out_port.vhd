-- an out port of an unconstrained type has no constraint either
entity unconstrained_out_port is
  port(y : out bit_vector);
end;
architecture rtl of unconstrained_out_port is
begin
end;
