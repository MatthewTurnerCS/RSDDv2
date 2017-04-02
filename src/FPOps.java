
public enum FPOps 
{
	// Operations that output new FP value
	ABS("fp.abs", 1, false),
	NEG("fp.neg", 1, false),
	PLUS("fp.add", 2, true),
	
	
	// Operations that output boolean
	LEQ("fp.leq", 2, false),
	LT("fp.lt", 2, false),
	GEQ("fp.geq", 2, false),
	GT("fp.gt", 2, false);
	
	
	protected String str;
	protected int arity;
	protected boolean doRound;
	
	FPOps (String string, int arity, boolean doRound){
	    this.str = string;
	    this.arity = arity;
	    this.doRound = doRound;
	  }
}