import java.util.Random;

public class SMTFloat 
{
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

	String sgn = "";
	String exp = "";
	String man = "";

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

	// eb is bits for exponent
	// sb is bits for significand, INCLUDING hidden bit

	public SMTFloat(int eb, int sb, Random r){
		sgn += nextBit(r);
		for(int i=0; i < eb; i++)
			exp += nextBit(r);
		for(int i=0; i < sb-1; i++){
			man += nextBit(r);
		}
	}

  public SMTFloat(int eb, int sb, SpecialCase option) {
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

    int sigBits = sb - 1;

    switch(option) {
      case NEG_INF:
      case POS_INF:
        exp += String.format("%0" + eb + "d", 1);
        man += String.format("%0" + sigBits + "d", 0);
        break;
      case NEG_ZERO:
      case POS_ZERO:
        exp += String.format("%0" + eb + "d", 0);
        man += String.format("%0" + sigBits + "d", 0);
        break;
      case NAN:
        exp += String.format("%0" + eb + "d", 1);
        man += String.format("%0" + sigBits + "d", 1);
        break;
    }
  }

	public static SMTFloat GenerateFloat(int bits, Random r){
		assert(bits == 16 || bits == 32 || bits == 64 || bits == 128);
		switch(bits){
		case 16:
      if (r.nextBoolean()) {
        return new SMTFloat(5, 11, r);
      }
      return new SMTFloat(5, 11, SpecialCase.getRandom(r));
		case 32:
      if (r.nextBoolean()) {
        return new SMTFloat(8, 24, r);
      }
      return new SMTFloat(8, 24, SpecialCase.getRandom(r));
		case 64:
      if (r.nextBoolean()) {
        return new SMTFloat(11, 53, r);
      }
      return new SMTFloat(11, 53, SpecialCase.getRandom(r));
		case 128:
      if (r.nextBoolean()) {
        return new SMTFloat(15, 113, r);
      }
      return new SMTFloat(15, 113, SpecialCase.getRandom(r));
		}

		return null;
	}

	@Override
	public String toString(){
		return "#b" + sgn + " " + "#b" + exp + " " + "#b" + man;
	}
}
