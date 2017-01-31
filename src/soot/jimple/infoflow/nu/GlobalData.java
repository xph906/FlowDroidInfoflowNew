package soot.jimple.infoflow.nu;

import java.util.HashMap;
import java.util.Map;

import soot.SootField;
import soot.SootMethod;
import soot.Unit;
import soot.jimple.Stmt;

import soot.jimple.toolkits.ide.icfg.BiDiInterproceduralCFG;
import soot.toolkits.graph.ExceptionalUnitGraph;
import soot.toolkits.graph.Orderer;
import soot.toolkits.graph.PseudoTopologicalOrderer;
import soot.toolkits.graph.UnitGraph;

public class GlobalData {
	private static GlobalData instance = null;
	public static GlobalData getInstance(){
		if(instance == null)
			instance = new GlobalData();
		return instance;
	}
	final private Map<String, Integer> viewIDMap = 
			new HashMap<String, Integer>();
	final private Map<String, Integer> layoutIDMap = 
			new HashMap<String, Integer>();
	final private Map<String, Integer> fieldIDMap = 
			new HashMap<String, Integer>();
	
	public static String getFieldKey(SootField sf){
		return sf.getDeclaringClass() + "@" + sf.getName()+"@"+sf.getType();
	}
	
	private GlobalData(){}
	
	public void addFieldID(SootField sf, Integer id){
		System.out.println("Stored Field ID: "+getFieldKey(sf)+" => "+id);
		//System.out.println("TODO: solve the duplicate cases");
		fieldIDMap.put(getFieldKey(sf), id);
	}
	
	public Integer getFieldID(SootField sf){
		return fieldIDMap.get(getFieldKey(sf));
	}
	
	public void addLayoutID(Stmt stmt, BiDiInterproceduralCFG<Unit, SootMethod> icfg, Integer id){
		SootMethod sm = icfg.getMethodOf(stmt);
		layoutIDMap.put(sm.getDeclaringClass().getName(), id);
		System.out.println("  StoreLayoutID: "+sm.getName()+" "+sm.getDeclaringClass().getName()+" ->"+id);
	}
	public Integer getLayoutID(String declaringClassName){
		return layoutIDMap.get(declaringClassName);
	}
	
	public void addViewID(String stmtTag, Integer id){
		viewIDMap.put(stmtTag, id);
	}
	
	public void addViewID(Stmt stmt, BiDiInterproceduralCFG<Unit, SootMethod> icfg, Integer id){
		if(!stmt.containsInvokeExpr() || !stmt.getInvokeExpr().getMethod().getName().equals("findViewById")){
			System.err.println("Error addViewID: stmt doesn't contain findViewById: "+stmt);
			return ;
		}
		SootMethod sm = icfg.getMethodOf(stmt);
		if(!sm.hasActiveBody()){
			System.err.println("Error addViewID: stmt is not in active method: "+sm);
			return ;
		}
		UnitGraph g = new ExceptionalUnitGraph(sm.getActiveBody());
	    Orderer<Unit> orderer = new PseudoTopologicalOrderer<Unit>();
	    int cnt = 0;
	    for (Unit u : orderer.newList(g, false)) {
	    	cnt++;
	    	if(stmt.equals((Stmt)u))
	    		break;
	    }
	    String sig = StmtPosTag.createStmtPosSignature(cnt, sm);
	    viewIDMap.put(sig, id);
	}
	
	public Integer getViewID(Stmt stmt, BiDiInterproceduralCFG<Unit, SootMethod> icfg){
		if(!stmt.containsInvokeExpr() || !stmt.getInvokeExpr().getMethod().getName().equals("findViewById")){
			System.err.println("Error getViewID: stmt doesn't contain findViewById: "+stmt);
			return null;
		}
		SootMethod sm = icfg.getMethodOf(stmt);
		if(!sm.hasActiveBody()){
			System.err.println("Error getViewID: stmt is not in active method: "+sm);
			return null;
		}
		UnitGraph g = new ExceptionalUnitGraph(sm.getActiveBody());
	    Orderer<Unit> orderer = new PseudoTopologicalOrderer<Unit>();
	    int cnt = 0;
	    for (Unit u : orderer.newList(g, false)) {
	    	cnt++;
	    	if(stmt.equals((Stmt)u))
	    		break;
	    }
	    String sig = StmtPosTag.createStmtPosSignature(cnt, sm);
	    return viewIDMap.get(sig);
	}
	
}
