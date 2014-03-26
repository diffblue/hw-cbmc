`define RNE 0
`define RNA 1
`define RTP 2
`define RTN 3
`define RTZ 4

// Normalises a denormal number or deal with catastrophic cancelation

module normaliseUp(
  input [9:0] uf_exponent_in,
  input [23:0] uf_significand_in,
  output reg [9:0] uf_exponent,
  output reg [23:0] uf_significand);

  reg [5:0] shift;
  
  always @(*) begin
    shift = 0;
    
    uf_exponent = uf_exponent_in;
    uf_significand = uf_significand_in;

    `ifdef 0
    if ((0xFFFF00 & uf->significand) == 0) {
      uf->significand <<= 16;
      shift += 16;
    }
    if ((0xFF0000 & uf->significand) == 0) {
      uf->significand <<= 8;
      shift += 8;
    }
    if ((0xF00000 & uf->significand) == 0) {
      uf->significand <<= 4;
      shift += 4;
    }
    if ((0xC00000 & uf->significand) == 0) {
      uf->significand <<= 2;
      shift += 2;
    }
    if ((0x800000 & uf->significand) == 0) {
      uf->significand <<= 1;
      shift += 1;
    }

    uf_exponent -= shift;
    `endif
  end // always

endmodule

`define BIAS 127

module unpack(
  input [31:0] f,
  output reg uf_nan, uf_inf, uf_zero, uf_subnormal, uf_sign,
  output reg [9:0] uf_exponent,
  output reg [23:0] uf_significand);

  wire sign;
  wire [7:0] exponent;
  wire [22:0] significand;

  // split up f
  assign { sign, exponent, significand } = f;      
  
  always @(*) begin
    uf_sign = sign;

    if (exponent == 0) begin
      if (significand == 0) begin
        //makeZero(&uf);
        end

      else begin
        uf_nan = 0;
        uf_inf = 0;
        uf_zero = 0;
        uf_subnormal = 1;

        uf_exponent = -126;
        uf_significand = significand;

        //normaliseUp(&uf);
        end
      end

    else if (exponent == 'hff) begin
      if (significand == 0) begin
        //makeInf(&uf);
        end
      else begin
        //makeNaN(&uf);
        end
      end

    else begin
      // Normal

      uf_nan = 0;
      uf_inf = 0;
      uf_zero = 0;
      uf_subnormal = 0;

      uf_exponent = exponent - `BIAS;
      uf_significand = 'h800000 | significand;
    end
  end // always
endmodule

module pack(
  input uf_nan, uf_inf, uf_zero, uf_subnormal, uf_sign,
  input [9:0] uf_exponent,
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
      end
    else if (uf_inf) begin
      exponent = 'hff;
      significand = 'h0;
      end
    else if (uf_zero) begin
      exponent = 'h0;
      significand = 'h0;
      end
    else if (uf_subnormal) begin
      biased = uf_exponent+`BIAS-1;
      exponent = 'h0;
      significand = uf_significand >> -biased;
      end
    else begin
      exponent = uf_exponent + `BIAS;
      significand = 'h7fffff & uf_significand; // Remove leading 1
    end
  end // always

  // staple together
  assign f = 123; //sign o exponent o significand;
  
endmodule

// Perform the actual increment caused by rounding and correct the
// exponent if needed.
module roundInc(); //(unpackedFloat *result, uint64_t increment) {
  `ifdef 0
  uint32_t incremented = result->significand + increment;

  if (incremented == (1<<24)) {
    assert((incremented & 0x1) == 0x0);
    incremented >>= 1;
    ++result->exponent;
    // Note that carrying into the exponent would be possible with
    // packed representations
  }

  assert(incremented < (1<<24));
  result->significand = incremented;
  `endif
endmodule

// Make the decision of whether to round or not.
module rounder(); // (int roundingMode, unpackedFloat *result, uint8_t guardBit, uint8_t stickyBit) {
  `ifdef 0

  uint64_t increment = 1;

  if (result->exponent < -150) {
    // Even rounding up will not make this representable
    makeZero(result);

    return;

  } else if (result->exponent < -126) {
    // For subnormals, correct the guard and sticky bits

    int subnormalAmount = -(result->exponent + 126);

    increment = 1 << subnormalAmount;
    
    stickyBit = stickyBit | guardBit | 
      ((((1 << (subnormalAmount - 1)) - 1) & result->significand) ? 1 : 0);

    guardBit = ((1 << (subnormalAmount - 1)) & result->significand) ? 1 : 0;

    result->significand &= ~(increment - 1);

  }


  /* Round to fixed significand length */
  switch (roundingMode) {
  case RNE :
    if (guardBit) {
      if (stickyBit || (result->significand & increment)) {
	roundInc(result, increment);
      }
    }
    break;

  case RNA :
    if (guardBit) {
	roundInc(result, increment);
    }
    break;

  case RTP :
    if ((result->sign == 0) && (guardBit || stickyBit)) {
      roundInc(result, increment);
    }
    break;

  case RTN :
    if ((result->sign == 1) && (guardBit || stickyBit)) {
      roundInc(result, increment);
    }
    break;

  case RTZ :
    // No rounding needed
    break;
  }


  /* Round to fixed exponent length */
  switch (roundingMode) {
  case RNE :
  case RNA :
    if (result->exponent > 127) {
      makeInf(result);
    }
    break;

  case RTP :
    if (result->exponent > 127) {
      if (result->sign == 0) {
	makeInf(result);
      } else {
	makeMax(result);
      }
    }
    break;

  case RTN :
    if (result->exponent > 127) {
      if (result->sign == 1) {
	makeInf(result);
      } else {
	makeMax(result);
      }
    }
    break;

  case RTZ :
    if (result->exponent > 127) {
      makeMax(result);
    }
    break;
  }

  if (result->exponent < -126) {
    result->subnormal = 1;
  }
  `endif
endmodule // rounder


module dualPathAdder(); //int isAdd, int roundingMode, unpackedFloat *uf, unpackedFloat *ug, unpackedFloat *result) {
  `ifdef 0
  unpackedFloat larger;
  unpackedFloat smaller;
  uint8_t guardBit = 0;
  uint8_t stickyBit = 0;

  /* Flags -- result will be normal unless otherwise marked */
  result->nan = 0;
  result->inf = 0;
  result->zero = 0;
  result->subnormal = 0;

  initUnpackedFloat(&larger);
  initUnpackedFloat(&smaller);

  /* Compute the difference between exponents */
  int exponentDifference = uf->exponent - ug->exponent;

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

  result->exponent = larger.exponent;

  /* Work out if it is an effective subtract */
  /*
  if (larger.sign == 0) {
    negateResult = 0;
    effectiveSubtract = ~isAdd ^ smaller.sign;
  } else {
    negateResult = 1;
    effectiveSubtract = isAdd ^ smaller.sign
  }
  */
  // Simplifies to ...

  int effectiveSubtract = larger.sign ^ (isAdd ? 0 : 1) ^ smaller.sign;

  // 'decimal point' after the 26th bit, LSB 2 bits are 0
  // 26 so that we can cancel one and still have 24 + guard bits
  uint32_t lsig = larger.significand << 2;
  uint32_t ssig = smaller.significand << 2;
  uint32_t sum = 0xFFFFFFFF;

  /* Split the two paths */
  if (exponentDifference <= 1) {

    /* Near path */

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

  } else {


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
    }
  }
  
  
  // Decimal point is after 26th bit
  sum = lsig + ssig;
  
  if (effectiveSubtract) {
    // Due to exponent difference, sum is either 25 or 26 bit
    assert((0xFC000000ul & sum) == 0x0);
    assert((0x03000000ul & sum) != 0x0);
    
    if (sum & 0x02000000ul) { // 26 bit
      sum <<= 1;
    } else {                  // 25 bit
      --result->exponent;
      sum <<= 2;
    }
    // Decimal point is now after the 27th bit
    
  } else {
    
    // sum is either 26 or 27 bits
    assert((0xF8000000ul & sum) == 0x0);
    assert((0x06000000ul & sum) != 0x0);
    
    if (sum & 0x04000000ul) { // 27 bit
      ++result->exponent;
    } else {                  // 26 bit
      sum <<= 1;
    }
  }
  
  
 extract:
  // Decimal point is now after the 27th bit
  result->significand = sum >> 3;
  guardBit = (sum >> 2) & 0x1;
  stickyBit |= (((sum >> 1) & 0x1) | (sum & 0x1));
  
  
  // Can be simplified as the subnormal case implies no rounding
 rounder :
  rounder(roundingMode, result, guardBit, stickyBit);
  
  `endif
endmodule // dualPathAdder

module fp_add_sub(
  input isAdd,
  input [2:0] roundingMode,
  input [31:0] f,
  input [31:0] g,
  output [31:0] result);

  // unpack f

  wire uf_nan, uf_inf, uf_zero, uf_subnormal, uf_sign;
  wire [9:0] uf_exponent;
  wire [23:0] uf_significand;

  unpack unpack_f(f, uf_nan, uf_inf, uf_zero, uf_subnormal, uf_sign, uf_exponent, uf_significand);

  // unpack g

  wire ug_nan, ug_inf, ug_zero, ug_subnormal, ug_sign;
  wire [9:0] ug_exponent;
  wire [23:0] ug_significand;
  
  unpack unpack_g(g, ug_nan, ug_inf, ug_zero, ug_subnormal, ug_sign, ug_exponent, ug_significand);
  
  // set up unpacked result

  reg result_nan, result_inf, result_zero, result_subnormal, result_sign;
  reg [9:0] result_exponent;
  reg [23:0] result_significand;

  always @(*) begin

    // Handle all the special cases

    if (uf_nan || ug_nan) begin
      result_nan = 1;
      result_inf = 0;
      result_zero = 0;
      result_subnormal = 0;
      result_exponent = 'hff;
      result_significand = 0;
      end

    else if (uf_inf) begin
      `ifdef 0
      if ((ug->inf) && 
          ((isAdd) ? uf->sign != ug->sign : uf->sign == ug->sign)) {
        makeNaN(result);
        return;
      } else {
        makeInf(result);
        result->sign = uf->sign;
        return;
      }
      `endif
      end

    else if (ug_inf) begin
      //makeInf(result);
      //result->sign = (isAdd) ? ug->sign : ~ug->sign;
      end

    else if (uf_zero) begin
      if (ug_zero) begin
        `ifdef 0
        makeZero(result);

        unsigned int flip = (isAdd) ? 0 : 1;

        if (roundingMode == RTN) {
  	  result->sign = uf->sign &  (flip ^ ug->sign);
  
        } else {
  	result->sign = uf->sign |  (flip ^ ug->sign);

        }
        return;
        `endif
        end
      
      else begin // ug_zero
        //*result = *ug;
        //result->sign = (isAdd) ? result->sign : ~result->sign;
        end
      end

    else if (ug_zero) begin
      //*result = *uf;
      end

    else begin
      //dualPathAdder(isAdd,roundingMode,uf,ug,result);
    end

  end // always

  // now pack the result

  pack pack_result(result_nan, result_inf, result_zero, result_subnormal,
                   result_sign, result_exponent, result_significand, result);

endmodule

`ifdef 0
float sub(int roundingMode, float f, float g) {
  unpackedFloat uf = unpack(f);
  unpackedFloat ug = unpack(g);
  unpackedFloat result;

  initUnpackedFloat(&result);

  addUnit(0,roundingMode,&uf,&ug,&result);
  //check(result);

  float res = pack(result);

  return res;
}
`endif
