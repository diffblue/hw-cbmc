// Rounding modes

`define RNE 0
`define RNA 1
`define RTP 2
`define RTN 3
`define RTZ 4

// Normalises a denormal number or deal with catastrophic cancelation

module normaliseUp(
  input signed [9:0] uf_exponent_in,
  input [23:0] uf_significand_in,
  output reg signed [9:0] uf_exponent,
  output reg [23:0] uf_significand);

  reg [5:0] shift;
  
  always @(*) begin
    shift = 0;
    
    uf_exponent = uf_exponent_in;
    uf_significand = uf_significand_in;

    if (('hffff00 & uf_significand) == 0) begin
      uf_significand = uf_significand << 16;
      shift = shift + 16;
    end
    
    if (('hff0000 & uf_significand) == 0) begin
      uf_significand = uf_significand << 8;
      shift = shift + 8;
    end
    
    if (('hf00000 & uf_significand) == 0) begin
      uf_significand = uf_significand << 4;
      shift = shift + 4;
    end
    
    if (('hc00000 & uf_significand) == 0) begin
      uf_significand = uf_significand << 2;
      shift = shift + 2;
    end
    
    if (('h800000 & uf_significand) == 0) begin
      uf_significand = uf_significand << 1;
      shift = shift + 1;
    end

    uf_exponent = uf_exponent - shift;
  end // always

endmodule

`define BIAS 127

module unpack(
  input [31:0] f,
  output reg uf_nan, uf_inf, uf_zero, uf_subnormal, uf_sign,
  output reg signed [9:0] uf_exponent,
  output reg [23:0] uf_significand);

  wire sign;
  wire [7:0] exponent;
  wire [22:0] significand;

  // split up f
  assign { sign, exponent, significand } = f;      
  
  wire signed [9:0] normaliseUp_exponent;
  wire [23:0] normaliseUp_significand;

  // this is used for the cae that the number is subnormal
  normaliseUp unpack_normaliseUp(
    -126, significand, normaliseUp_exponent, normaliseUp_significand);
  
  always @(*) begin
    uf_sign = sign;

    if (exponent == 0) begin
      if (significand == 0) begin
        // make zero
        uf_nan = 0;
        uf_inf = 0;
        uf_zero = 1;
        uf_subnormal = 0;
        uf_exponent = 0;
        uf_significand = 0;
      end else begin
        // subnormal
        uf_nan = 0;
        uf_inf = 0;
        uf_zero = 0;
        uf_subnormal = 1;

        uf_exponent = -126;
        uf_significand = normaliseUp_significand;
      end
    end else if (exponent == 'hff) begin
      if (significand == 0) begin
        // make infinity
        uf_nan = 0;
        uf_inf = 1;
        uf_zero = 0;
        uf_subnormal = 0; 
        uf_exponent = 'hff;
        uf_significand = 0;
      end else begin
        // make NaN
        uf_nan = 1;
        uf_inf = 0;
        uf_zero = 0;
        uf_subnormal = 0;
        uf_exponent = 'hff;
        uf_significand = 0;
      end
    end else begin
      // Normal
      uf_nan = 0;
      uf_inf = 0;
      uf_zero = 0;
      uf_subnormal = 0;

      uf_exponent = exponent - `BIAS;
      uf_significand = 'h800000 | significand;
    end // if
  end // always
endmodule

module pack(
  input uf_nan, uf_inf, uf_zero, uf_subnormal, uf_sign,
  input signed [9:0] uf_exponent,
  input [23:0] uf_significand,
  output [31:0] f);
  
  reg sign;
  reg [7:0] exponent;
  reg [22:0] significand;
  
  reg [8:0] biased;

  always @(*) begin
    sign = uf_sign;

    if (uf_nan) begin
      exponent = 'hff;
      significand = 'h40b2bd;  // qNaN
    end else if (uf_inf) begin
      exponent = 'hff;
      significand = 'h0;
    end else if (uf_zero) begin
      exponent = 'h0;
      significand = 'h0;
    end else if (uf_subnormal) begin
      biased = uf_exponent+`BIAS-1;
      exponent = 'h0;
      significand = uf_significand >> -biased;
    end else begin
      exponent = uf_exponent + `BIAS;
      significand = 'h7fffff & uf_significand; // Remove leading 1
    end
  end // always

  // staple together
  assign f = 123; //sign o exponent o significand;
  
endmodule


// Make the decision of whether to round or not.
module rounder(
  input [2:0] roundingMode,
  input result_nan_in, result_inf_in, result_zero_in, result_subnormal_in, result_sign_in,
  input [9:0] result_exponent_in,
  input [23:0] result_significand_in,
  output reg result_nan, result_inf, result_zero, result_subnormal, result_sign,
  output reg [9:0] result_exponent,
  output reg [23:0] result_significand,
  input guardBit,
  input stickyBit);

  reg [63:0] increment;
  reg [63:0] incremented;  
  reg [31:0] subnormalAmount;
  reg do_increment;

  always @(*) begin
  
    // copy over
    result_nan=result_nan_in;
    result_inf=result_inf_in;
    result_zero=result_zero_in;
    result_subnormal=result_subnormal_in;
    result_sign=result_sign_in;
    result_exponent=result_exponent_in;
    result_significand=result_significand_in;

    increment = 1;

    if (result_exponent < -150) begin
      // Even rounding up will not make this representable; make zero.
      result_nan = 0;
      result_inf = 0;
      result_zero = 1;
      result_subnormal = 0;
      result_exponent = 0;
      result_significand = 0;
    end else begin
      if (result_exponent < -126) begin
        // For subnormals, correct the guard and sticky bits

        subnormalAmount = -(result_exponent + 126);

        increment = 1 << subnormalAmount;
        
        //stickyBit = stickyBit | guardBit | 
        //  ((((1 << (subnormalAmount - 1)) - 1) & result->significand) ? 1 : 0);

        //guardBit = ((1 << (subnormalAmount - 1)) & result->significand) ? 1 : 0;

        result_significand = result_significand & ~(increment - 1);
      end

      // Round to fixed significand length

      case (roundingMode)
        `RNE: do_increment = guardBit & (stickyBit || (result_significand & increment));
        `RNA: do_increment = guardBit;
        `RTP: do_increment = !result_sign && (guardBit || stickyBit);
        `RTN: do_increment = result_sign && (guardBit || stickyBit);
        `RTZ: do_increment = 0; // No rounding needed
        default: do_increment = 0;
      endcase
      
      // the following case corresponds to calling roundInc
      if (do_increment) begin
        incremented = result_significand + increment;

        if (incremented == (1<<24)) begin
          incremented = incremented >> 1;
          result_exponent = result_exponent + 1;
          // Note that carrying into the exponent would be possible with
          // packed representations
        end
        
        result_significand = incremented;
      end

      // Round to fixed exponent length
      case (roundingMode)
        `RNE:
          if (result_exponent > 127) begin
            // make infinity
            result_nan = 0;
            result_inf = 1;
            result_zero = 0;
            result_subnormal = 0;
            result_exponent = 'hff;
            result_significand = 0;            
          end

        `RNA:
          if (result_exponent > 127) begin
            // make infinity
            result_nan = 0;
            result_inf = 1;
            result_zero = 0;
            result_subnormal = 0;
            result_exponent = 'hff;
            result_significand = 0;            
          end

        `RTP:
          if (result_exponent > 127) begin
            if (result_sign == 0) begin
              // make infinity
              result_nan = 0;
              result_inf = 1;
              result_zero = 0;
              result_subnormal = 0;
              result_exponent = 'hff;
              result_significand = 0;            
            end else begin
              // make max
              result_nan = 0;
              result_inf = 0;
              result_zero = 0;
              result_subnormal = 0;
              result_exponent = 127;
              result_significand = 'hffffff;
            end
          end
        
        `RTN:
          if (result_exponent > 127) begin
            if (result_sign == 1) begin
              // make infinity
              result_nan = 0;
              result_inf = 1;
              result_zero = 0;
              result_subnormal = 0;
              result_exponent = 'hff;
              result_significand = 0;            
            end else begin
              // make max
              result_nan = 0;
              result_inf = 0;
              result_zero = 0;
              result_subnormal = 0;
              result_exponent = 127;
              result_significand = 'hffffff;
            end
          end

        `RTZ:
          if (result_exponent > 127) begin
            // make max
            result_nan = 0;
            result_inf = 0;
            result_zero = 0;
            result_subnormal = 0;
            result_exponent = 127;
            result_significand = 'hffffff;
          end
      endcase

      if (result_exponent < -126)
        result_subnormal = 1;
    end // if

  end // always
  
endmodule // rounder


module dualPathAdder(
  input isAdd,
  input [2:0] roundingMode,
  input uf_nan, uf_inf, uf_zero, uf_subnormal, uf_sign,
  input [9:0] uf_exponent,
  input [23:0] uf_significand,
  input ug_nan, ug_inf, ug_zero, ug_subnormal, ug_sign,
  input [9:0] ug_exponent,
  input [23:0] ug_significand,
  output reg result_nan, result_inf, result_zero, result_subnormal, result_sign,
  output reg [9:0] result_exponent,
  output reg [23:0] result_significand);

  reg guardBit;
  reg stickyBit;

  reg [9:0] larger_exponent, smaller_exponent;
  reg [23:0] larger_significand, smaller_significant;
  reg signed [10:0] exponentDifference;
  reg effectiveSubtract;
  
  always @(*) begin

    guardBit = 0;
    stickyBit = 0;

    // Flags -- result will be normal unless otherwise marked
    result_nan = 0;
    result_inf = 0;
    result_zero = 0;
    result_subnormal = 0;

    // Compute the difference between exponents
    exponentDifference = uf_exponent - ug_exponent;

    `ifdef 0
    /* Order by exponent */
    if ((exponentDifference > 0) || 
        ((exponentDifference == 0) && (uf->significand > ug->significand))) {
      larger = *uf;
      smaller = *ug;
      result->sign = larger.sign;

    } else {
      larger = *ug;
      smaller = *uf;
      exponentDifference = -exponentDifference;
      result->sign = isAdd ? larger.sign : ~larger.sign;

    }
    `endif

    result_exponent = larger_exponent;

    // Work out if it is an effective subtract
    effectiveSubtract = larger_sign ^ (isAdd ? 0 : 1) ^ smaller_sign;

    `ifdef 0
    // 'decimal point' after the 26th bit, LSB 2 bits are 0
    // 26 so that we can cancel one and still have 24 + guard bits
    uint32_t lsig = larger_significand << 2;
    uint32_t ssig = smaller_significand << 2;
    uint32_t sum = 'hffffffff;
    `endif

    // Split the two paths
    if (exponentDifference <= 1) begin

      /* Near path */

      `ifdef 0
      // Align
      ssig >>= exponentDifference;


      if (effectiveSubtract) {

        /* May have catestrophic cancelation */

        uint32_t diff = lsig - ssig;

        assert((diff & 0xFC000000) == 0);  // result is up to 26 bit

        if (diff == 0) {  // Fully cancelled

          makeZero(result);

          /* IEEE-754 2008 says:
           * When the sum of two operands with opposite signs (or the
           * difference of two operands with like signs) is exactly
           * zero, the sign of that sum (or difference) shall be +0 in
           * all rounding-direction attributes except
           * roundTowardNegative; under that attribute, the sign of an
           * exact zero sum (or difference) shall be −0. However, x + x
           * = x − (−x) retains the same sign as x even when x is zero.
           */
          result->sign = (roundingMode == RTN) ? 1 : 0;
          return; // No need to round

        } else if (diff & 0x02000000) { // 26 bit result

          sum = diff << 1;

          // Sticky bits are 0
          assert((sum & 0x3) == 0);

          goto extract;

        } else { // Some cancelation

          --result->exponent;
          result->significand = diff >> 1;
          guardBit = 0;
          stickyBit = 0;

          normaliseUp(result);

          // Won't underflow due to an exciting property of subnormal
          // numbers.  Also, clearly, won't overflow.  Furthermore,
          // won't increment.  Thus don't need to call the rounder -- as
          // long as the subnormal flag is correctly set.
          
          //	goto rounder;

          result->subnormal = (result->exponent < -126) ? 1 : 0;
          return;
        }

      } else {

        // Near addition is the same as far addition
        // except without the need to align first.
        // Thus fall through...
      }
      `endif

    end else begin

      `ifdef 0
      /* Far path */
      if (exponentDifference > 26) {
        
        result->significand = larger.significand;
        result->subnormal = larger.subnormal;
        return;
        
      } else {
        
        if (effectiveSubtract) {
          ssig = (~ssig) + 1;
        }
        
        // Align
        int i;

        for (i = 1; i <= 26; i <<= 1) {
          if (exponentDifference & i) {
            uint32_t iOnes = ((1<<i) - 1);
            stickyBit |= ((ssig & iOnes) ? 1 : 0);
            
            // Sign extending shift
            if (effectiveSubtract) {
              ssig = (ssig >> i) | (iOnes << (32 - i));
            } else {
              ssig = (ssig >> i);
            }
            
          }
        }
      `endif
    end

    `ifdef 0    
    // Decimal point is after 26th bit
    sum = lsig + ssig;
    
    if (effectiveSubtract) begin
      if (sum & 0x02000000ul) { // 26 bit
        sum <<= 1;
      } else {                  // 25 bit
        --result_exponent;
        sum <<= 2;
      }
      // Decimal point is now after the 27th bit
      end
    else begin
      if (sum & 0x04000000ul)
        ++result_exponent;
      else
        sum <<= 1;
    end
    
   extract:
    // Decimal point is now after the 27th bit
    result_significand = sum >> 3;
    guardBit = (sum >> 2) & 0x1;
    stickyBit |= (((sum >> 1) & 0x1) | (sum & 0x1));
    
    // Can be simplified as the subnormal case implies no rounding
   rounder:
    rounder(roundingMode, result, guardBit, stickyBit);
    `endif
    
  end // always

endmodule // dualPathAdder

module fp_add_sub(
  input isAdd,
  input [2:0] roundingMode,
  input [31:0] f,
  input [31:0] g,
  output [31:0] result);

  // unpack f

  wire uf_nan, uf_inf, uf_zero, uf_subnormal, uf_sign;
  wire signed [9:0] uf_exponent;
  wire [23:0] uf_significand;

  unpack unpack_f(f, uf_nan, uf_inf, uf_zero, uf_subnormal, uf_sign, uf_exponent, uf_significand);

  // unpack g

  wire ug_nan, ug_inf, ug_zero, ug_subnormal, ug_sign;
  wire signed [9:0] ug_exponent;
  wire [23:0] ug_significand;
  
  unpack unpack_g(g, ug_nan, ug_inf, ug_zero, ug_subnormal, ug_sign, ug_exponent, ug_significand);
  
  // instantiate the dual-path adder

  wire dp_nan, dp_inf, dp_zero, dp_subnormal, dp_sign;
  wire signed [9:0] dp_exponent;
  wire [23:0] dp_significand;  

  dualPathAdder dualPathadder(
    isAdd, roundingMode,
    uf_nan, uf_inf, uf_zero, uf_subnormal, uf_sign, uf_exponent, uf_significand,
    ug_nan, ug_inf, ug_zero, ug_subnormal, ug_sign, ug_exponent, ug_significand,
    dp_nan, dp_inf, dp_zero, dp_subnormal, dp_sign, dp_exponent, dp_significand);

  // set up unpacked result

  reg result_nan, result_inf, result_zero, result_subnormal, result_sign;
  reg signed [9:0] result_exponent;
  reg [23:0] result_significand;
  
  // internal variable
  reg flip;
  
  always @(*) begin

    // Handle all the special cases

    if (uf_nan || ug_nan) begin
      // make NaN
      result_nan = 1;
      result_inf = 0;
      result_zero = 0;
      result_subnormal = 0;
      result_exponent = 'hff;
      result_significand = 0;
    end else if (uf_inf) begin
      if (ug_inf && 
          ((isAdd) ? uf_sign != ug_sign : uf_sign == ug_sign)) begin
        // make NaN
        result_nan = 1;
        result_inf = 0;
        result_zero = 0;
        result_subnormal = 0;
        result_exponent = 'hff;
        result_significand = 0;
      end else begin
        // make infinity
        result_nan = 0;
        result_inf = 1;
        result_zero = 0;
        result_subnormal = 0;
        result_exponent = 'hff;
        result_significand = 0;                    
        result_sign = uf_sign;
      end
    end else if (ug_inf) begin
      // make infinity
      result_nan = 0;
      result_inf = 1;
      result_zero = 0;
      result_subnormal = 0;
      result_exponent = 'hff;
      result_significand = 0;                    
      result_sign = (isAdd) ? ug_sign : !ug_sign;
    end else if (uf_zero) begin
      if (ug_zero) begin
        // make zero
        result_nan = 0;
        result_inf = 0;
        result_zero = 1;
        result_subnormal = 0;
        result_exponent = 0;
        result_significand = 0;

        flip = (isAdd) ? 0 : 1;

        if (roundingMode == `RTN)
  	  result_sign = uf_sign & (flip ^ ug_sign);
        else 
          result_sign = uf_sign | (flip ^ ug_sign);

      end else begin // !ug_zero
        // copy ug
        result_nan=ug_nan;
        result_inf=ug_inf;
        result_zero=ug_zero;
        result_subnormal=ug_subnormal;
        result_sign=ug_sign;
        result_exponent=ug_exponent;
        result_significand=ug_significand;
        
        // adjust sign
        result_sign = isAdd ? result_sign : !result_sign;
      end
    end else if (ug_zero) begin
      // copy uf
      result_nan=uf_nan;
      result_inf=uf_inf;
      result_zero=uf_zero;
      result_subnormal=uf_subnormal;
      result_sign=uf_sign;
      result_exponent=uf_exponent;
      result_significand=uf_significand;
    end else begin
      // use output from dual-path adder
      result_nan=dp_nan;
      result_inf=dp_inf;
      result_zero=dp_zero;
      result_subnormal=dp_subnormal;
      result_sign=dp_sign;
      result_exponent=dp_exponent;
      result_significand=dp_significand;
    end

  end // always

  // now pack the result

  pack pack_result(result_nan, result_inf, result_zero, result_subnormal,
                   result_sign, result_exponent, result_significand, result);

endmodule
