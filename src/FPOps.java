/**
 * Represents Floating Point operations supported by SMT-LIB 2.0
 */
public enum FPOps 
{
	// Operations that output new FP value
	ABS("fp.abs", 1, false),
	NEG("fp.neg", 1, false),
	PLUS("fp.add", 2, true),
	SUB("fp.sub", 2, true),
	MUL("fp.mul", 2, true),
	DIV("fp.div", 2, true),
	FMA("fp.fma", 3, true),
	SQRT("fp.sqrt", 1, true),
	REM("fp.rem", 2, false),
	ROUNDTOINTEGRAL("fp.roundToIntegral", 1, true),
	MIN("fp.min", 2, false),
	MAX("fp.max", 2, false),

	// Operations that output boolean value
	LEQ("fp.leq", 2, false),
	LT("fp.lt", 2, false),
	GEQ("fp.geq", 2, false),
	GT("fp.gt", 2, false),
	EQ("fp.eq", 2, false),
	ISNORMAL("fp.isNormal", 1, false),
	ISSUBNORMAL("fp.isSubnormal", 1, false),
	ISZERO("fp.isZero", 1, false),
	ISINFINITE("fp.isInfinite", 1, false),
	ISNAN("fp.isNaN", 1, false),
	ISNEGATIVE("fp.isNegative", 1, false),
	ISPOSITIVE("fp.isPositive", 1, false);

	// SMT-LIB string representing this operation
	protected String str;

	// Number of arguments this operator applies to
	protected int arity;

	// Set to true if this operation needs a rounding mode specified
	protected boolean doRound;

	FPOps (String string, int arity, boolean doRound){
		this.str = string;
		this.arity = arity;
		this.doRound = doRound;
	}
}