`define basic
`basic
`define with_value value
`with_value
`define uses_previous `with_value
`uses_previous
`define with_parameter(a, b, c) a-b-c
`with_parameter(x, y, z)
`with_parameter(x, y, `with_value)
`with_parameter (moo, foo, bar)
`define no_parameter (1+2)
`no_parameter
