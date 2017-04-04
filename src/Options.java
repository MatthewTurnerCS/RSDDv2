import java.util.*;


public class Options 
{
	/**
	 * @return A HashMap mapping parameter names to default values
	 */
	public static HashMap<String, Object> getDefaults(){

		// Number of nodes to initially generate for each category
		int numFuncs = 1;
		int numPreds = 1;
		int numVars = 2;
		int numConsts = 2;

		// Number of nodes to derive from operators/functions/predicates
		int numDerivedFloats = 5;
		int numDerivedBools = 5;

		// Random generator: Can be seeded using command-line
		Random r = new Random();

		// Bit vector enabling/disabling Float16/32/64/128 nodes
		short mode = 0b1111;

		// min/max args for functions and predicates
		int minArgs = 1;
		int maxArgs = 3;

		// Max number of clauses (CNF) and max variables per clause (CNF/RANDOM)
		int clauseCountMax = 6;
		int clauseSizeMax = 3;

		// Max recursion depth (RANDOM)
		int maxDepth = 3;

		// % chances of using special floats (e.g. NaN), predicates, and functions instead of purely random floats and operators
		int specialChance = 20;
		int predChance = 20;
		int funcChance = 20;

		// Store the defaults in a map and return it
		HashMap<String, Object> defaults = new HashMap<String, Object>();
		defaults.put("numFuncs", numFuncs);
		defaults.put("numPreds", numPreds);
		defaults.put("numVars", numVars);
		defaults.put("numConsts", numConsts);
		defaults.put("numDerivedFloats", numDerivedFloats);
		defaults.put("numDerivedBools", numDerivedBools);
		defaults.put("r", r);
		defaults.put("mode", mode);
		defaults.put("minArgs", minArgs);
		defaults.put("maxArgs", maxArgs);		
		defaults.put("clauseCountMax", clauseCountMax);
		defaults.put("clauseSizeMax", clauseSizeMax);
		defaults.put("maxDepth", maxDepth);		
		defaults.put("specialChance", specialChance);
		defaults.put("predChance", predChance);
		defaults.put("funcChance", funcChance);		
		return defaults;
	}

	/**
	 * For "-<arg>" in <args>, maps <arg> to the next int in <args>
	 * Special case: -mode is mapped to the next short, -r is mapped to a random number generator seeded at next int
	 * @param args - Command line arguments
	 * @param options - Map to be modified
	 */
	public static void parseArgs(String[] args, HashMap<String, Object> options){
		for(int i=0; i < args.length; i+=2){
			if(args[i].equals("-r")){
				options.put("r", new Random(Integer.parseInt(args[i+1])));
			} else if(args[i].equals("-mode")){
				options.put("mode", Short.parseShort(args[i+1]));
			} else {
				options.put(args[i].substring(1), Integer.parseInt(args[i+1]));
			}
		}
	}
}