import java.util.*;

public class FPFuzzer 
{
	private static int selectRandValRange (Random r, int min, int max){
		int result;		
		result = r.nextInt(max - min + 1) + min;
		return result;
	}

	static int funcCounter = 0;
	static int predCounter = 0;

	private static ArrayList<SMTNode> boolNodes = new ArrayList<SMTNode>();
	private static ArrayList<SMTNode> floatNodes = new ArrayList<SMTNode>();
	private static ArrayList<SMTNode> funcNodes = new ArrayList<SMTNode>();
	private static ArrayList<SMTNode> predNodes = new ArrayList<SMTNode>();

	private static void generateFunctions(int numFuncs, int minArgs, int maxArgs, short mode, Random r){ 
		int numArgs;
		Signature sig;
		ArrayList<SMTType> operandTypes;
		String name;
		StringBuilder builder;
		builder = new StringBuilder();
		for (int i = 0; i < numFuncs; i++){
			name = "f" + funcCounter++;
			numArgs = selectRandValRange (r, minArgs, maxArgs);			
			operandTypes = new ArrayList<SMTType>(numArgs);

			for (int j = 0; j < numArgs; j++) {
				int bw = SMTFloat.randomBitWidth(r, mode);
				operandTypes.add (new FloatType(bw));
			}

			int bw = SMTFloat.randomBitWidth(r, mode);
			FloatType retType = new FloatType(bw);

			sig = new Signature (operandTypes, retType);
			builder.append("(declare-fun ");
			funcNodes.add (new SMTNode(new FuncType(name, sig), name));

			builder.append (name);
			builder.append(" (");
			for (int j = 0; j < numArgs; j++) {
				if(j!= 0) builder.append (" ");
				builder.append (operandTypes.get(j).toString());
			}
			builder.append(")");
			builder.append(" " + retType);
			builder.append (")\n");
		}		
		System.out.print (builder.toString());		
	}

	private static void generatePredicates(int numPreds, int minArgs, int maxArgs, short mode, Random r){ 
		int numArgs;
		Signature sig;
		ArrayList<SMTType> operandTypes;
		String name;
		StringBuilder builder;
		builder = new StringBuilder();
		for (int i = 0; i < numPreds; i++){
			name = "p" + predCounter++;
			numArgs = selectRandValRange (r, minArgs, maxArgs);			
			operandTypes = new ArrayList<SMTType>(numArgs);

			for (int j = 0; j < numArgs; j++) {
				int bw = SMTFloat.randomBitWidth(r, mode);
				operandTypes.add (new FloatType(bw));
			}
			sig = new Signature (operandTypes, BoolType.boolType);
			builder.append("(declare-fun ");
			predNodes.add (new SMTNode(new FuncType(name, sig), name));

			builder.append (name);
			builder.append(" (");
			for (int j = 0; j < numArgs; j++) {
				if(j!= 0) builder.append (" ");
				builder.append (operandTypes.get(j).toString());
			}
			builder.append(")");
			builder.append(" Bool");
			builder.append (")\n");
		}		
		System.out.print (builder.toString());		
	}

	private static void generateInputs(int numVars, int numConsts, short mode, Random r){ 
		StringBuilder builder = new StringBuilder();
		String name;

		System.out.println("; GENERATING VARIABLES");
		for(int i=0; i < numVars; i++){
			name = "?float" + SMTNode.getNodeCtr();
			int bw = SMTFloat.randomBitWidth(r, mode);

			builder.append("(declare-const ");
			builder.append(name);
			builder.append(" Float");
			builder.append(bw);
			builder.append(")\n");
			floatNodes.add (new SMTNode (new FloatType(bw), name));
		}
		System.out.print(builder.toString());
		builder = new StringBuilder();

		System.out.println("; GENERATING CONSTS");
		for (int i = 0; i < numConsts; i++) {
			name = "?float" + SMTNode.getNodeCtr();

			int bw = SMTFloat.randomBitWidth(r, mode);			
			SMTFloat floatConst = SMTFloat.GenerateFloat(bw, r);

			builder.append("(declare-const ");
			builder.append(name);
			builder.append(" Float" + bw);
			builder.append(")\n");
			builder.append("(assert (= " + name + " (fp " + floatConst.toString() + ")))\n");			
			floatNodes.add (new SMTNode (new FloatType(bw), name));
		}


		System.out.print (builder.toString());		
	}

	private static String adaptBW(SMTNode node, int bits, Random r) throws Exception{
		String name = node.name;

		if(((FloatType)node.type).bits == bits){
			return name;
		}

		// Pick random round mode
		FPRoundMode[] rModes = FPRoundMode.values();
		FPRoundMode rMode = rModes[(r.nextInt(rModes.length))];
		
		switch(bits){
		case 16:
			return "((_ to_fp 5 11) " + rMode + " " + name + ")";			
		case 32:
			return "((_ to_fp 8 24) " + rMode + " " + name + ")";
		case 64:
			return "((_ to_fp 11 53) " + rMode + " " + name + ")";
		case 128:
			return "((_ to_fp 15 113) " + rMode + " " + name + ")";
		default:
			throw new Exception("unsupported");
		}
	}

	private static void deriveFloats(int numDerivedFloats, Random r) throws Exception{ 
		System.out.println("; DERIVE FLOATS");
		StringBuilder builder = new StringBuilder();

		// TODO use functions as well as ops
		for(int i=0; i < numDerivedFloats; i++){
			// Pick random rounding mode
			FPRoundMode[] rModes = FPRoundMode.values();
			FPRoundMode rMode = rModes[(r.nextInt(rModes.length))];
			Object[] ops = EnumSet.range(FPOps.ABS, FPOps.PLUS).toArray();

			String name = "?float" + SMTNode.getNodeCtr();

			// Pick random operation that outputs float
			FPOps op = (FPOps)ops[r.nextInt(ops.length)];

			ArrayList<SMTNode> args = new ArrayList<SMTNode>();
			for(int argc=0; argc < op.arity; argc++){
				args.add(floatNodes.get(r.nextInt(floatNodes.size())));
			}

			// Randomly pick an arg and use its bitwidth
			int idx = r.nextInt(args.size());
			int bw = ((FloatType)args.get(idx).type).bits;

			builder.append("(declare-const " + name + " Float" + bw + ")\n");
			builder.append("(assert (= " + name + " " + "(" + op.str + " "); 

			if(op.doRound){
				builder.append(rMode + " ");
			}

			for(SMTNode arg: args){
				builder.append(adaptBW(arg, bw, r) + " ");
			}
			builder.deleteCharAt(builder.toString().length()-1);

			builder.append(")))\n");

			SMTNode derived = new SMTNode(new FloatType(bw), name);		
			floatNodes.add(derived);
		}
		System.out.print(builder.toString());
	}

	private static void deriveBools(int numDerivedBools, Random r) throws Exception{ 
		System.out.println("; DERIVE BOOLS");
		StringBuilder builder = new StringBuilder();

		for(int i=0; i<numDerivedBools; i++){
			// Pick random rounding mode
			FPRoundMode[] rModes = FPRoundMode.values();
			FPRoundMode rMode = rModes[(r.nextInt(rModes.length))];
			Object[] ops = EnumSet.range(FPOps.LEQ, FPOps.GT).toArray();

			String name = "?bool" + SMTNode.getNodeCtr();

			// Pick random operation that outputs boolean
			// TODO Use predicates as well
			FPOps op = (FPOps)ops[r.nextInt(ops.length)];
			ArrayList<SMTNode> args = new ArrayList<SMTNode>();
			for(int argc=0; argc < op.arity; argc++){
				args.add(floatNodes.get(r.nextInt(floatNodes.size())));
			}

			// Randomly pick an arg and use its bitwidth
			int idx = r.nextInt(args.size());
			int bw = ((FloatType)args.get(idx).type).bits;

			builder.append("(declare-const " + name + " Bool)\n");
			builder.append("(assert (= " + name + " " + "(" + op.str + " ");

			if(op.doRound){
				builder.append(rMode + " ");
			}

			for(SMTNode arg: args){		
				builder.append(adaptBW(arg, bw, r) + " ");
			}
			builder.deleteCharAt(builder.toString().length()-1);

			builder.append(")))\n");

			SMTNode derived = new SMTNode(BoolType.boolType, name);
			boolNodes.add(derived);
		}
		System.out.print(builder.toString());
	}

	private static void combineBools(BooleanLayerKind blk){
		System.out.println("; FINAL ASSERT");
		StringBuilder builder = new StringBuilder();
		switch(blk){
		case AND:
		case OR:
			String op = (blk == BooleanLayerKind.AND)? "and ": "or ";
			builder.append("(assert (");
			builder.append(op);
			for(SMTNode boolNode: boolNodes){
				builder.append(boolNode.name + " ");
			}
			builder.deleteCharAt(builder.toString().length()-1);
			builder.append("))");
			System.out.println(builder.toString());
			break;

		// TODO other modes
		case CNF:
		case RANDOM:
			// TODO
			break;

		}
	}

	private enum FPRoundMode {
		RNE,	// Round nearest ties to even
		RNA,	// Round nearest ties to away
		RTP,	// Round toward positive
		RTN,	// Round toward negative
		RTZ		// Round toward zero
	}

	private enum BooleanLayerKind {
		AND,
		OR,
		CNF,
		RANDOM;
	}

	public static void main(String[] args) throws Exception{
		HashMap<String, Object> options = Options.getDefaults();
		Options.parseArgs(args, options);

		int numFuncs = 1;
		int numPreds = 1;
		int numVars = 2;
		int numConsts = 2;		
		int numDerivedFloats = 2;
		int numDerivedBools = 3;
		Random r = new Random(); // TODO seed
		short mode = 0b1111;
		int minArgs = 1;
		int maxArgs = 3;
		BooleanLayerKind combineMode = BooleanLayerKind.AND;
		
		// TODO Support setting to non-default values via command-line flags
		// TODO min-ref system?
		
		generateFunctions(numFuncs, minArgs, maxArgs, mode, r);
		generatePredicates(numPreds, minArgs, maxArgs, mode, r);
		generateInputs(numVars, numConsts, mode, r);
		deriveFloats(numDerivedFloats, r);
		deriveBools(numDerivedBools, r);
		combineBools(combineMode);
		System.out.println("(check-sat)");
	}
}