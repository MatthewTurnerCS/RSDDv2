import java.util.Random;

public class SMTFloat 
{
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

	public static SMTFloat GenerateFloat(int bits, Random r){
		assert(bits == 16 || bits == 32 || bits == 64 || bits == 128);
		switch(bits){
		case 16:
			return new SMTFloat(5, 11, r);
		case 32:
			return new SMTFloat(8, 24, r);
		case 64:
			return new SMTFloat(11, 53, r);
		case 128:
			return new SMTFloat(15, 113, r);
		}

		return null;
	}

	@Override
	public String toString(){
		return "#b" + sgn + " " + "#b" + exp + " " + "#b" + man;
	}
}