/*
** jasper-adder.c
**
** Copyright Martin Brain
** martin.brain@cs.ox.ac.uk
** 13/02/14
**
** A relatively naive implementation of a dual-path adder for 
** IEEE-754 binary32 (single precision float).  This includes packing
** and unpacking, rounding and handling of subnormal numbers.
**
** To analyse with CBMC run:
**  $ cbmc --function addSpecRNE fp_adder.c
**
*/

#include <assert.h>
#include <math.h>
#include <stdint.h>

// Packed structure for manipulating encoded numbers

typedef struct _packedFloat {
  unsigned int significand:23;
  unsigned int exponent:8;
  unsigned int sign:1;
} packedFloat;

typedef union _mix {
  float f;
  packedFloat b;
} mix;



// Unpacked structure for actual use

typedef struct _bitpattern {
  unsigned int nan:1;
  unsigned int inf:1;
  unsigned int zero:1;
  unsigned int subnormal:1;

  unsigned int sign:1;
  int exponent:10;              // Bias removed
  unsigned int significand:24;  // Leading 1 added
} unpackedFloat;


// Rounding modes

#define RNE 0
#define RNA 1
#define RTP 2
#define RTN 3
#define RTZ 4


// Note that C's == does not give bitwise equality
int compareFloat (float f, float g) {
#ifdef CUT
  // For signed zeros
  mix mf;
  mix mg;

  mf.f = f;
  mg.f = g;

  return ((mf.b == mg.b) || (isnan(f) && isnan(g)));
#else
  return ((f == g) || (isnan(f) && isnan(g)));
#endif
}


// Functions for working with unpacked floats
void initUnpackedFloat (unpackedFloat *uf) {
  uf->nan = 1;
  uf->inf = 1;
  uf->zero = 1;
  uf->subnormal = 1;

  uf->sign = 1;
  uf->exponent = -512;
  uf->significand = 0xFFFFFF;
  return;
}

void makeZero (unpackedFloat *uf) {
  uf->nan = 0;
  uf->inf = 0;
  uf->zero = 1;
  uf->subnormal = 0;

  uf->exponent = 0;
  uf->significand = 0;
  return;
}

void makeInf (unpackedFloat *uf) {
  uf->nan = 0;
  uf->inf = 1;
  uf->zero = 0;
  uf->subnormal = 0;

  uf->exponent = 0xFF;
  uf->significand = 0;
  return;
}

void makeMax (unpackedFloat *uf) {
  uf->nan = 0;
  uf->inf = 0;
  uf->zero = 0;
  uf->subnormal = 0;

  uf->exponent = 127;
  uf->significand = 0xFFFFFF;
  return;
}

void makeNaN (unpackedFloat *uf) {
  uf->nan = 1;
  uf->inf = 0;
  uf->zero = 0;
  uf->subnormal = 0;

  uf->exponent = 0xFF;
  uf->significand = 0;
}


#define BIAS 127

// Invariants for the use of the unpacked float
void check (unpackedFloat uf) {
  assert(((unsigned int)uf.nan + 
          (unsigned int)uf.inf +
          (unsigned int)uf.zero +
          (unsigned int)uf.subnormal) <= 1);

  if (uf.nan == 1) {
    assert(uf.exponent == 0xFF);
    assert(uf.significand == 0x0);

  } else if (uf.inf == 1) {
    assert(uf.exponent == 0xFF);
    assert(uf.significand == 0x0);

  } else if (uf.zero) {
    assert(uf.exponent == 0x0);
    assert(uf.significand == 0x0);

  } else if (uf.subnormal) {
    assert(uf.exponent < -126);
    assert(uf.significand != 0x0);

    int biased = (uf.exponent + BIAS) - 1;

    assert(biased <= 0);
    assert(biased >= -23);
    assert((uf.significand & 0x800000) == 0x800000);  // Normalised
    assert((uf.significand & ((1 << -biased) - 1)) == 0x0); // Correctly rounded

  } else {
    assert(uf.exponent >= -126);
    assert(uf.exponent <=  127);
    assert(uf.significand != 0x0);
    assert((uf.significand & 0x800000) == 0x800000);

  }

  return;
}


// Normalises a denormal number or deal with catastrophic cancelation
int normaliseUp (unpackedFloat *uf) {
  int shift = 0;

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

  uf->exponent -= shift;
  return shift;
}



unpackedFloat unpack (float f) {
  unpackedFloat uf;
  mix m;

  m.f = f;

  initUnpackedFloat(&uf);
  uf.sign = m.b.sign;

  if (m.b.exponent == 0) {
    if (m.b.significand == 0) {
      makeZero(&uf);

    } else {
      uf.nan = 0;
      uf.inf = 0;
      uf.zero = 0;
      uf.subnormal = 1;

      uf.exponent = -126;
      uf.significand = m.b.significand;

      normaliseUp(&uf);
    }

  } else if (m.b.exponent == 0xFF) {
    if (m.b.significand == 0) {
      makeInf(&uf);
    } else {
      makeNaN(&uf);
    }

  } else {
    // Normal

    uf.nan = 0;
    uf.inf = 0;
    uf.zero = 0;
    uf.subnormal = 0;

    uf.exponent = m.b.exponent - BIAS;
    uf.significand = 0x800000 | m.b.significand;
  }

  return uf;
}


float pack (unpackedFloat uf) {
  mix m;

  m.b.sign = uf.sign;

  if (uf.nan == 1) {
    m.b.exponent = 0xFF;
    m.b.significand = 0x40B2BD;  // qNaN

  } else if (uf.inf == 1) {
    m.b.exponent = 0xFF;
    m.b.significand = 0x0;

  } else if (uf.zero) {
    m.b.exponent = 0x0;
    m.b.significand = 0x0;

  } else if (uf.subnormal) {
    int biased = (uf.exponent + BIAS) - 1;

    m.b.exponent = 0x0;
    m.b.significand = (uf.significand >> -biased);
    
  } else {
    m.b.exponent = (int)uf.exponent + BIAS;
    m.b.significand = 0x7FFFFF & ((unsigned int)uf.significand); // Remove leading 1
  }

  return m.f;
}


// Perform the actual increment caused by rounding and correct the
// exponent if needed.
void roundInc (unpackedFloat *result, uint64_t increment) {
  assert((increment & (increment - 1)) == 0x0);   // Is a single bit
  assert(((increment - 1) & result->significand) == 0x0); // Increment affects least bit
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
  return;
}

// Make the decision of whether to round or not.
void rounder (int roundingMode, unpackedFloat *result, uint8_t guardBit, uint8_t stickyBit) {

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

  return;
}




void dualPathAdder(int isAdd, int roundingMode, unpackedFloat *uf, unpackedFloat *ug, unpackedFloat *result) {
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
        
        //        goto rounder;

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
  
  return;
}





void addUnit (int isAdd, int roundingMode, unpackedFloat *uf, unpackedFloat *ug, unpackedFloat *result) {

  // Handle the special cases
  if (uf->nan || ug->nan) {
    makeNaN(result);
    return;

  } else if (uf->inf) {
    if ((ug->inf) && 
        ((isAdd) ? uf->sign != ug->sign : uf->sign == ug->sign)) {
      makeNaN(result);
      return;
    } else {
      makeInf(result);
      result->sign = uf->sign;
      return;
    }

  } else if (ug->inf) {
    makeInf(result);
    result->sign = (isAdd) ? ug->sign : ~ug->sign;
    return;

  } else if (uf->zero) {
    if (ug->zero) {
      makeZero(result);

      unsigned int flip = (isAdd) ? 0 : 1;

      if (roundingMode == RTN) {
        result->sign = uf->sign &  (flip ^ ug->sign);

      } else {
        result->sign = uf->sign |  (flip ^ ug->sign);

      }
      return;

    } else {
      *result = *ug;
      result->sign = (isAdd) ? result->sign : ~result->sign;
      return;
    }

  } else if (ug->zero) {
    *result = *uf;
    return;

  } else {

    dualPathAdder(isAdd,roundingMode,uf,ug,result);

    return;
  }

  // Should be unreachable
  assert(0);
  return;
}



float add(int roundingMode, float f, float g) {
  unpackedFloat uf = unpack(f);
  unpackedFloat ug = unpack(g);
  unpackedFloat result;

  initUnpackedFloat(&result);

  addUnit(1,roundingMode,&uf,&ug,&result);
  //check(result);

  float res = pack(result);

  return res;
}


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








  /********************** SPECS! **************************/

void packerSpec (float f) {
  unpackedFloat uf;
  float result;

  uf = unpack(f);
  check(uf);
  result = pack(uf);
  f = f;

  assert(compareFloat(f,result));
}


void addSpecRNE (float f, float g) {
  float real = f + g;
  float actual = add(RNE,f,g);

  assert(compareFloat(real,actual));
}

void subSpecRNE (float f, float g) {
  float real = f - g;
  float actual = sub(RNE,f,g);

  assert(compareFloat(real,actual));
}

