import java.util.*;

/**
 * Generates a syntactically valid random SMT-LIB string for QF_FP logic
 * @author Sam Olds
 * @author Matthew Turner
 *
 */
public class FPFuzzer 
{
	/**
	 * Generates a random value in the range [min, max]
	 * @param r - Random generator
	 * @param min - Lower bound
	 * @param max - Upper bound
	 * @return A random value in the range [min, max]
	 */
	private static int selectRandValRange (Random r, int min, int max){
		int result;		
		result = r.nextInt(max - min + 1) + min;
		return result;
	}

	// Counters for generated functions/predicates
	static int funcCounter = 0;
	static int predCounter = 0;

	// Lists of SMTNodes divided by type
	// No type guarantees: Ensure node has expected content before adding it!
	private static ArrayList<SMTNode> boolNodes = new ArrayList<SMTNode>();
	private static ArrayList<SMTNode> floatNodes = new ArrayList<SMTNode>();
	private static ArrayList<SMTNode> funcNodes = new ArrayList<SMTNode>();
	private static ArrayList<SMTNode> predNodes = new ArrayList<SMTNode>();

	/**
	 * Generates signatures for functions with random floating point input(s) and floating point output
	 * @param numFuncs - Number of nodes to generate
	 * @param minArgs - Minimum number of arguments
	 * @param maxArgs - Maximum number of arguments
	 * @param mode - Use value in [1, 15]: Used as bit vector flags: enables generating Float16/32/64/128 values
	 * @param r - Random generator
	 */
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

	/**
	 * Generates signatures for functions with random floating point input(s) and boolean output
	 * @param numPreds - Number of nodes to generate
	 * @param minArgs - Minimum number of arguments
	 * @param maxArgs - Maximum number of arguments
	 * @param mode - Use value in [1, 15]: Used as bit vector flags: enables generating Float16/32/64/128 values
	 * @param r - Random generator
	 */
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

	/**
	 * Generates initial constant and variable floating point nodes
	 * @param numVars - Number of floating point variables to generate
	 * @param numConsts - Number of floating point constants to generate
	 * @param mode - Use value in [1, 15]: Used as bit vector flags: enables generating Float16/32/64/128 values
	 * @param r - Random generator
	 * @param specialChance - % chance of randomly using hard-coded infinite/zero/NaN float instead of purely random bits
	 */
	private static void generateInputs(int numVars, int numConsts, short mode, Random r, int specialChance){ 
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
			SMTFloat floatConst = SMTFloat.GenerateFloat(bw, r, specialChance);

			builder.append("(declare-const ");
			builder.append(name);
			builder.append(" Float" + bw);
			builder.append(")\n");
			builder.append("(assert (= " + name + " (fp " + floatConst.toString() + ")))\n");			
			floatNodes.add (new SMTNode (new FloatType(bw), name));
		}


		System.out.print (builder.toString());		
	}

	/**
	 * Returns a String equivalent to a <bits>-width Float version of <node> in SMT-LIB format
	 * @param node - Node being adapted
	 * @param bits - Desired bit width
	 * @param r - Random generator
	 * @return An SMT-LIB format string representing the given node adapted to the provided bit-width
	 * @throws Exception - Generic Exception thrown if bits is not one of {16, 32, 64, 128}
	 */
	private static String adaptBW(SMTNode node, int bits, Random r) throws Exception{
		String name = node.name;

		// Already a match: Just return the nodes name
		if(((FloatType)node.type).bits == bits){
			return name;
		}

		// Pick random round mode
		FPRoundMode[] rModes = FPRoundMode.values();
		FPRoundMode rMode = rModes[(r.nextInt(rModes.length))];

		// Use appropriate syntax to adapt this node
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

	/**
	 * Generates new floating point nodes using supported operators or generated functions
	 * @param numDerivedFloats - Number of nodes to generate
	 * @param r - Random generator
	 * @param funcChance - % chance of using function instead of operator
	 * @throws Exception - Generic exception thrown if call to adaptBW fails
	 */
	private static void deriveFloats(int numDerivedFloats, Random r, int funcChance) throws Exception{ 
		System.out.println("; DERIVE FLOATS");
		StringBuilder builder = new StringBuilder();

		for(int i=0; i < numDerivedFloats; i++){
			// Pick random rounding mode
			FPRoundMode[] rModes = FPRoundMode.values();
			FPRoundMode rMode = rModes[(r.nextInt(rModes.length))];

			String name = "?float" + SMTNode.getNodeCtr();

			if (r.nextInt(100) < funcChance) {
				int idx = r.nextInt(funcNodes.size());
				FuncType node = (FuncType)funcNodes.get(idx).getType();
				Signature sig = node.getSignature();
				List<SMTType> ops = sig.getOperandTypes();
				SMTType resultType = sig.getResultType();

				builder.append("(declare-const " + name + " Float" + ((FloatType)resultType).bits + ")\n");
				builder.append("(assert (= " + name + " " + "(" + node.toString() + " "); 

				for (int argc=0; argc < ops.size(); argc++){
					SMTNode randNode = floatNodes.get(r.nextInt(floatNodes.size()));
					FloatType currNode = (FloatType)ops.get(argc);
					int bw = currNode.bits;
					builder.append(adaptBW(randNode, bw, r) + " ");
				}

				builder.deleteCharAt(builder.toString().length()-1);
				builder.append(")))\n");

				SMTNode derived = new SMTNode(new FloatType(((FloatType)resultType).bits), name);
				floatNodes.add(derived);
			} else {
				Object[] ops = EnumSet.range(FPOps.ABS, FPOps.MAX).toArray();

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
		}
		System.out.print(builder.toString());
	}

	/**
	 * Generates new boolean nodes using supported operators or generated predicates
	 * @param numDerivedBools - Number of nodes to generate
	 * @param r - Random generator
	 * @param predChance - % chance of using predicate instead of operator
	 * @throws Exception - Generic exception thrown if call to adaptBW fails
	 */
	private static void deriveBools(int numDerivedBools, Random r, int predChance) throws Exception{ 
		System.out.println("; DERIVE BOOLS");
		StringBuilder builder = new StringBuilder();

		for(int i=0; i<numDerivedBools; i++){
			// Pick random rounding mode
			FPRoundMode[] rModes = FPRoundMode.values();
			FPRoundMode rMode = rModes[(r.nextInt(rModes.length))];

			String name = "?bool" + SMTNode.getNodeCtr();

			if (r.nextInt(100) < predChance) {
				int idx = r.nextInt(predNodes.size());
				FuncType node = (FuncType)predNodes.get(idx).getType();
				Signature sig = node.getSignature();
				List<SMTType> ops = sig.getOperandTypes();

				builder.append("(declare-const " + name + " Bool)\n");
				builder.append("(assert (= " + name + " " + "(" + node.toString() + " "); 

				for (int argc=0; argc < ops.size(); argc++){
					SMTNode randNode = floatNodes.get(r.nextInt(floatNodes.size()));
					FloatType currNode = (FloatType)ops.get(argc);
					int bw = currNode.bits;
					builder.append(adaptBW(randNode, bw, r) + " ");
				}

				builder.deleteCharAt(builder.toString().length()-1);
				builder.append(")))\n");

				SMTNode derived = new SMTNode(BoolType.boolType, name);
				boolNodes.add(derived);
			} else {
				Object[] ops = EnumSet.range(FPOps.LEQ, FPOps.ISPOSITIVE).toArray();

				// Pick random operation that outputs boolean
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
		}
		System.out.print(builder.toString());
	}

	/**
	 * Combines boolean nodes into a final assertion
	 * @param blk - Mode for performing combination of boolean nodes
	 * @param r - Random generator
	 * @param clauseCountMax - Max number of clauses (CNF)
	 * @param clauseSizeMax - Max variables per clause (CNF and RANDOM)
	 * @param maxDepth - Max recursion depth (RANDOM)
	 */
	private static void combineBools(BooleanLayerKind blk, Random r, int clauseCountMax, int clauseSizeMax,
			int maxDepth){
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
		case CNF:
			int clauseCount = r.nextInt(clauseCountMax) + 1;
			builder.append("(assert (and ");
			for (int i = 0; i < clauseCount; i++) {
				int clauseSize = r.nextInt(clauseSizeMax) + 1;
				builder.append("(or ");
				for (int j = 0; j < clauseSize; j++ ) {
					int randIdx = r.nextInt(boolNodes.size());
					builder.append(boolNodes.get(randIdx).name + " ");
				}
				builder.deleteCharAt(builder.toString().length()-1);
				builder.append(") ");
			}
			builder.deleteCharAt(builder.toString().length()-1);
			builder.append("))");
			System.out.println(builder.toString());
			break;
		case RANDOM:
			builder.append("(assert ");
			generateRandomBoolTree(builder, r, maxDepth, clauseSizeMax);
			builder.deleteCharAt(builder.toString().length()-1);
			builder.append(")");
			System.out.println(builder.toString());
			break;
		}
	}

	/**
	 * Recursively constructs a tree of random OR/AND operators
	 * @param builder - StringBuilder containing SMT-LIB format string
	 * @param r - Random generator
	 * @param maxDepth - Max recursion depth
	 * @param clauseSizeMax - Max variables per clause
	 */
	private static void generateRandomBoolTree(StringBuilder builder, Random r,
			int maxDepth, int clauseSizeMax) {
		// Randomly pick AND/OR operator
		String op = (r.nextBoolean()) ? "(and " : "(or ";
		builder.append(op);

		// Randomly create a clause with clauseSize variables...
		int clauseSize = r.nextInt(clauseSizeMax) + 1;
		for (int j = 0; j < clauseSize; j++ ) {
			int randIdx = r.nextInt(boolNodes.size());
			if (maxDepth > 0 && r.nextBoolean()) {
				// If we can still recurse, with 50% chance build a subtree
				generateRandomBoolTree(builder, r, maxDepth - 1, clauseSizeMax);
			} else {
				// With 50% chance use a random variable (100% if at recursion depth limit)
				builder.append(boolNodes.get(randIdx).name + " ");
			}
		}

		builder.deleteCharAt(builder.toString().length()-1);
		builder.append(") ");
	}

	// Rounding mode
	public enum FPRoundMode {
		RNE,	// Round nearest ties to even
		// RNA,	// Round nearest ties to away // not supported by mathsat5
		RTP,	// Round toward positive
		RTN,	// Round toward negative
		RTZ		// Round toward zero
	}

	// Mode for creating final assertion from boolean layer
	public enum BooleanLayerKind {
		AND,
		OR,
		CNF,
		RANDOM;
	}

	/**
	 * Entry-point for this application: 
	 * Generates a syntactically valid random SMT-LIB string for QF_FP logic
	 * @param args: See Options.java
	 * @throws Exception: No effort is made to catch exceptions as a result of invalid args or failed calls to adaptBW
	 */
	public static void main(String[] args) throws Exception{

		// Get default parameter values; overwrite with cmd-line args when possible
		HashMap<String, Object> options = Options.getDefaults();
		BooleanLayerKind combineMode = BooleanLayerKind.RANDOM;
		Options.parseArgs(args, options);

		// Set parameters to match options
		int numFuncs = (int)options.get("numFuncs");
		int numPreds = (int)options.get("numPreds");
		int numVars = (int)options.get("numVars");
		int numConsts = (int)options.get("numConsts");		
		int numDerivedFloats = (int)options.get("numDerivedFloats");
		int numDerivedBools = (int)options.get("numDerivedBools");
		Random r = (Random)options.get("r");
		short mode = (short)options.get("mode");
		int minArgs = (int)options.get("minArgs");
		int maxArgs = (int)options.get("maxArgs");		
		int clauseCountMax = (int)options.get("clauseCountMax");
		int clauseSizeMax = (int)options.get("clauseSizeMax");
		int maxDepth = (int)options.get("maxDepth");
		int specialChance = (int)options.get("specialChance");
		int predChance = (int)options.get("predChance");
		int funcChance = (int)options.get("funcChance");

		// Special case for parsing combineMode enum
		for(int i=0; i < args.length; i++){
			if(args[i].equals("-combineMode")){
				if(args[i+1].equals("AND"))
					combineMode = BooleanLayerKind.AND;
				else if(args[i+1].equals("OR"))
					combineMode = BooleanLayerKind.OR;
				else if(args[i+1].equals("CNF"))
					combineMode = BooleanLayerKind.CNF;
				else if(args[i+1].equals("RANDOM"))
					combineMode = BooleanLayerKind.RANDOM;
			}
		}

		// Generate each layer based on parameters		
		// Input layer:
		generateFunctions(numFuncs, minArgs, maxArgs, mode, r);
		generatePredicates(numPreds, minArgs, maxArgs, mode, r);
		generateInputs(numVars, numConsts, mode, r, specialChance);

		// Derived Layers:
		deriveFloats(numDerivedFloats, r, funcChance);
		deriveBools(numDerivedBools, r, predChance);

		// Boolean Layer:
		combineBools(combineMode, r, clauseCountMax, clauseSizeMax, maxDepth);		
		System.out.println("(check-sat)");
	}
}
