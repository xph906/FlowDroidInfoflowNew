package soot.jimple.infoflow.nu;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import heros.InterproceduralCFG;
import soot.SootField;
import soot.SootMethod;
import soot.Unit;
import soot.jimple.Stmt;
import soot.jimple.infoflow.solver.cfg.IInfoflowCFG;
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
	final private Set<Stmt> sensitiveUISource = 
			new HashSet<Stmt>();
	final private Map<String, Integer> viewIDMap = 
			new HashMap<String, Integer>();
	final private Map<String, Integer> layoutIDMap = 
			new HashMap<String, Integer>();
	final private Map<String, Integer> fieldIDMap = 
			new HashMap<String, Integer>();
	final private Map<String, List<String>> dynamicViewTextMap =
			new HashMap<String, List<String>>();
	final private Map<String, Integer> dynamicViewStmtIDMap = 
			new HashMap<String, Integer>();
	boolean enableInterComponent = false;
	
	public void setEnableInterComponent(boolean flag){
		this.enableInterComponent = flag;
	}
	public boolean enableInterComponent(){
		return this.enableInterComponent;
	}
	
	public static String getFieldKey(SootField sf){
		return sf.getDeclaringClass() + "@" + sf.getName()+"@"+sf.getType();
	}
	
	private GlobalData(){}
	
	private boolean allowModification = true;
	private IInfoflowCFG icfg = null;
	
	public void setICFG(IInfoflowCFG icfg){
		this.icfg = icfg;
	}
	
	public IInfoflowCFG getICFG(){
		return icfg;
	}
	
	public void setAllowModification(boolean flag){
		this.allowModification = flag;
	}
	
	public String createStmtSignature(Stmt stmt, IInfoflowCFG cfg){
		SootMethod sm = cfg.getMethodOf(stmt);
		if(sm == null)
			return stmt.toString()+"@null@POSnull";
		
		String methodName = sm.getSignature();
		StringBuilder sb = new StringBuilder();
		sb.append(stmt.toString()+"@"+methodName+"@POS:");
		if(!sm.hasActiveBody()){
			sb.append("null");
			return sb.toString();
		}
		UnitGraph g = new ExceptionalUnitGraph(sm.getActiveBody());
	    Orderer<Unit> orderer = new PseudoTopologicalOrderer<Unit>();
	    int cnt = 0;
	    for (Unit u : orderer.newList(g, false)) {
	    	cnt++;
	    	if(stmt == (Stmt)u)
	    		break;
	    }
	    sb.append(cnt);
	    return sb.toString();
	}
	
	public void addSensitiveUISource(Stmt stmt, IInfoflowCFG cfg){
		if(!allowModification)
			return ;
		sensitiveUISource.add(stmt);
//		System.out.println("Added sensitiveStmt:"+sensitiveUISource.size());
//		for(Stmt s : sensitiveUISource){
//			System.out.println("  T:"+s.toString());
//			System.out.println("  S:"+createStmtSignature(s, cfg));
//		}
	}
	
	public boolean isSensitiveUISource(Stmt stmt){
		return sensitiveUISource.contains(stmt);
	}
	
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
	
	public void addTextToDyanmicView(Stmt view, String text, BiDiInterproceduralCFG<Unit, SootMethod> cfg){
		String key = this.createStmtSignature(view, (IInfoflowCFG)cfg);
		List<String> texts = this.dynamicViewTextMap.get(key);
		if(texts == null){
			texts = new ArrayList<String>();
			dynamicViewTextMap.put(key, texts);
		}
		texts.add(text);
		if(!dynamicViewStmtIDMap.containsKey(key))
			dynamicViewStmtIDMap.put(key, dynamicViewStmtIDMap.size()+1);
	}
	
	public String getDynamicViewType(Integer id){
		String key = null;
		for(Entry<String, Integer> entry : dynamicViewStmtIDMap.entrySet()){
			if(entry.getValue() == id){
				key = entry.getKey();
				break;
			}
		}
		if(key != null){
			String[] tmp = key.split("@");
			if (tmp.length > 0){
				tmp = tmp[0].split("new");
				if(tmp.length > 1)
					key = tmp[1].trim();
			}
		}
		return key;
	}
	
	public String getDynamicTextsFromViewID(Integer id){
		String key = null;
		for(Entry<String, Integer> pair : dynamicViewStmtIDMap.entrySet()){
			if(pair.getValue() == id){
				key = pair.getKey();
				break;
			}
		}
		if(key==null) return null;
		
		List<String> rs = dynamicViewTextMap.get(key);
		if(rs == null) return null;
		StringBuilder sb = new StringBuilder();
		for(String str : rs)
			sb.append(str+",");
		return sb.toString();
	}
	
	public Integer getDynamicViewID(Stmt view, BiDiInterproceduralCFG<Unit, SootMethod> cfg){
		if(cfg == null)
			cfg = icfg;
		String key = this.createStmtSignature(view, (IInfoflowCFG)cfg);
		return this.dynamicViewStmtIDMap.get(key);
	}
	
	public List<String> getDynamicViewTexts(Stmt view,  IInfoflowCFG cfg){
		return dynamicViewTextMap.get(createStmtSignature(view, cfg));
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