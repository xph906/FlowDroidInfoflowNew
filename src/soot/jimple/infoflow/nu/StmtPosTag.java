package soot.jimple.infoflow.nu;

import soot.SootMethod;
import soot.tagkit.AttributeValueException;
import soot.tagkit.Tag;

public class StmtPosTag implements Tag {
	final static public String TAG_NAME = "StmtPosTag";
	final String pos;
	public static String createStmtPosSignature(int cnt, SootMethod enclosingMethod){
		return "Line:"+cnt+"@"+enclosingMethod.getSignature();
	}
	
	public StmtPosTag(int cnt, SootMethod sm){
		this.pos = createStmtPosSignature(cnt, sm);
	}
	@Override
	public String getName() {
		return TAG_NAME;
	}

	@Override
	public byte[] getValue() throws AttributeValueException {
		// TODO Auto-generated method stub
		return this.pos.getBytes();
	}
	
	public String getPos(){
		return this.pos;
	}
	
	public String toString(){
		return TAG_NAME+":"+pos;
	}

}
