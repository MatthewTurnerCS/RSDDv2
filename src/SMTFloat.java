import java.util.Random;

/**
 * Represents literals for floating point constants in SMT-LIB format
 * @author Sam Olds
 * @author Matthew Turner
 *
 */
public class SMTFloat 
{
	// Enum for special hard-coded cases: See constructor
	private enum SpecialCase {
		NEG_INF,
		POS_INF,
		NEG_ZERO,
		POS_ZERO,
		NAN;

		public static SpecialCase getRandom(Random r) {
			return values()[r.nextInt(values().length)];
		}
	}

	// Bit vector strings for each component
	String sgn = "";
	String exp = "";
	String man = "";

	/**
	 * Returns a random bit-width from {16, 32, 64, 128} subject to fpMode constraint
	 * @param r - Random generator
	 * @param fpMode - Value in [1, 15] to be used as bit-vector enabling/disabling Float16/32/64/128
	 * @return A random bit-width from {16, 32, 64, 128} subject to fpMode constraint
	 */
	public static int randomBitWidth(Random r, short fpMode){
		assert(fpMode > 0 && fpMode < 16);		
		while(true)
		{
			switch(r.nextInt(4))
			{
			case 0:
				if((fpMode & 8) == 8){
					return 16;
				}
			case 1:
				if((fpMode & 4) == 4){
					return 32;
				}
			case 2:
				if((fpMode & 2) == 2){
					return 64;
				}
			case 3:
				if((fpMode & 1) == 1){
					return 128;
				}	    	  
			}
		}
	}

	private int nextBit(Random r){
		return r.nextInt(2);
	}

	/**
	 * Generates a random floating point literal with eb exponent bits and mb mantissa bits
	 * @param eb - Number of bits for exponent
	 * @param sb - Number of bits for mantissa
	 * @param r - Random generator
	 */
	public SMTFloat(int eb, int mb, Random r){
		sgn += nextBit(r);
		for(int i=0; i < eb; i++)
			exp += nextBit(r);
		for(int i=0; i < mb-1; i++){
			man += nextBit(r);
		}
	}

	/**
	 * Generates a floating point literal matching the special case <option>
	 * @param eb - Number of bits in exponent
	 * @param mb - Number of bits in mantissa
	 * @param option - The special case to use: See the SpecialCase enum
	 */
	public SMTFloat(int eb, int mb, SpecialCase option) {
		switch(option) {
		case NEG_INF:
		case NEG_ZERO:
		case NAN:
			sgn += "1";
			break;
		case POS_INF:
		case POS_ZERO:
			sgn += "0";
			break;
		}

		int manBits = mb - 1;

		switch(option) {
		case NEG_INF:
		case POS_INF:
			exp += String.format("%0" + eb + "d", 1);
			man += String.format("%0" + manBits + "d", 0);
			break;
		case NEG_ZERO:
		case POS_ZERO:
			exp += String.format("%0" + eb + "d", 0);
			man += String.format("%0" + manBits + "d", 0);
			break;
		case NAN:
			exp += String.format("%0" + eb + "d", 1);
			man += String.format("%0" + manBits + "d", 1);
			break;
		}
	}

	/**
	 * 
	 * @param bits - Bit width in {16, 32, 64, 128}
	 * @param r - Random generator
	 * @param specialChance - % chance of using SpecialCase instead of purely random bits
	 * @return An SMTFloat object representing an SMT-LIB floating point constant
	 */
	public static SMTFloat GenerateFloat(int bits, Random r, int specialChance){
		assert(bits == 16 || bits == 32 || bits == 64 || bits == 128);
		switch(bits){
		case 16:
			if (r.nextInt(100) < specialChance) {
				return new SMTFloat(5, 11, r);
			}
			return new SMTFloat(5, 11, SpecialCase.getRandom(r));
		case 32:
			if (r.nextInt(100) < specialChance) {
				return new SMTFloat(8, 24, r);
			}
			return new SMTFloat(8, 24, SpecialCase.getRandom(r));
		case 64:
			if (r.nextInt(100) < specialChance) {
				return new SMTFloat(11, 53, r);
			}
			return new SMTFloat(11, 53, SpecialCase.getRandom(r));
		case 128:
			if (r.nextInt(100) < specialChance) {
				return new SMTFloat(15, 113, r);
			}
			return new SMTFloat(15, 113, SpecialCase.getRandom(r));
		}

		return null;
	}
	
	@Override
	/**
	 * Returns a String of the form #b<signbit> #b<exponentbits> #b<mantissabits>
	 */
	public String toString(){
		return "#b" + sgn + " " + "#b" + exp + " " + "#b" + man;
	}
}