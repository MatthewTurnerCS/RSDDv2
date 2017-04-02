
public class FuncType extends SMTType {

	String name;
	Signature sig;
	
	public FuncType(String n, Signature s){
		name = n;
		sig = s;
	}
	
	@Override
	public String toString() { 
		return name;
	}
	
	public Signature getSignature(){
		return sig;
	}
}