/*******************************************************************\

Module: Verilog Lowering

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_VERILOG_LOWERING_H
#define CPROVER_VERILOG_LOWERING_H

class exprt;
class typet;

exprt verilog_lowering(exprt);
typet verilog_lowering(typet);

#endif
