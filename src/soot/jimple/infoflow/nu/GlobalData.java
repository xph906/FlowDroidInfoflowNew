package soot.jimple.infoflow.nu;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import nu.NUDisplay;
import heros.InterproceduralCFG;
import soot.SootField;
import soot.SootMethod;
import soot.Unit;
import soot.jimple.InvokeExpr;
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
	final private Set<String> sensitiveUISource = 
			new HashSet<String>();
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
	final private Map<String, Set<String>> internetURLAddrMap = 
			new HashMap<String, Set<String>>();
	private final Map<String, Set<String>> clsStringMap = 
			new HashMap<String, Set<String>>();
	
	private final Map<String, Integer> unsolvedViewStmtFlowIdMap = 
			new HashMap<String, Integer>();
	private final Set<String> classWithUnsolvedLayoutSet = 
			new HashSet<String>();
	private final Map<String, String> unsolvedURLSinkOriginalStmtMap = 
			new HashMap<String, String>();
	
	private final Map<String, Set<String>> cls2ImageNameMap =
			new HashMap<String, Set<String>>();
	
	private boolean allowSensitiveUISourceUpdate = true;
	
	public void addUnsolvedViewStmtFlowIdMap(String signature, Integer flowId){
		unsolvedViewStmtFlowIdMap.put(signature, flowId);
	}
	public void addStringToCls(String clsName, String texts){
		if(clsStringMap.containsKey(clsName))
			clsStringMap.get(clsName).add(texts.trim());
		else{
			Set<String> set = new HashSet<String>();
			set.add(texts.trim());
			clsStringMap.put(clsName, set);
		}
	}
	public void addImageNameToCls(String clsName, String imageName){
		if(cls2ImageNameMap.containsKey(clsName))
			cls2ImageNameMap.get(clsName).add(imageName.trim());
		else{
			Set<String> set = new HashSet<String>();
			set.add(imageName.trim());
			cls2ImageNameMap.put(clsName, set);
		}
	}
	public Set<String> getClsImageNames(String clsName){
		return cls2ImageNameMap.get(clsName);
	}
	public Map<String, Integer> getUnsolvedViewStmtFlowIdMap(){
		return unsolvedViewStmtFlowIdMap;
	}
	public Set<String> getClsStrings(String clsName){
		return clsStringMap.get(clsName);
	}
	public Set<String> getClsNameWithStrings(){
		return clsStringMap.keySet();
	}
	
	public static String getFieldKey(SootField sf){
		return sf.getDeclaringClass() + "@" + sf.getName()+"@"+sf.getType();
	}
	
	private GlobalData(){}
	
	
	private IInfoflowCFG icfg = null;
	
	public void setICFG(IInfoflowCFG icfg){
		this.icfg = icfg;
	}
	
	public IInfoflowCFG getICFG(){
		return icfg;
	}
	
	public void setAllowSensitiveUISourceUpdate(boolean flag){
		this.allowSensitiveUISourceUpdate = flag;
	}
	
	public void addInternetSinkURL(Stmt sink, String url, SootMethod sm){
//		String sig = ToolSet.createStmtSignature(sink, null);
		String sig = FlowPathSet.getStmtSignatureForDynamicCombination(sink, sm);
		String[] urls = url.split(",");
//		System.out.println("DEBUG222:"+url);
//		for(String u : urls){
//			System.out.println("  :"+u);
//		}
		
		if(internetURLAddrMap.containsKey(sig))
			internetURLAddrMap.get(sig).add(url.toLowerCase());
		else{
			Set<String> tmp = new HashSet<String>();
			tmp.add(url.toLowerCase());
			internetURLAddrMap.put(sig, tmp);
		}
	}
	public void addUnsolvedUrlSinkOriginalStmt(Stmt sink, SootMethod sinkMethod, Stmt ori, SootMethod originMethod){
		this.unsolvedURLSinkOriginalStmtMap.put(FlowPathSet.getStmtSignatureForDynamicCombination(sink, sinkMethod),
				FlowPathSet.getStmtSignatureForDynamicCombination(ori, originMethod));
	}
	
	public Set<String> getInternetSinkURL(Stmt sink, SootMethod sm){
//		String sig = ToolSet.createStmtSignature(sink, null);
		String sig = FlowPathSet.getStmtSignatureForDynamicCombination(sink, sm);
		return internetURLAddrMap.get(sig);
	}
	public String getUnsolvedUrlSinkOriginalStmt(Stmt stmt, SootMethod sm){
		return unsolvedURLSinkOriginalStmtMap.get(FlowPathSet.getStmtSignatureForDynamicCombination(stmt, sm));
	}
	//createStmtSignature
//	public String createStmtSignature(Stmt stmt, IInfoflowCFG cfg){
//		SootMethod sm = cfg.getMethodOf(stmt);
//		if(sm == null)
//			return stmt.toString()+"@null@POSnull";
//		
//		String methodName = sm.getSignature();
//		StringBuilder sb = new StringBuilder();
//		sb.append(stmt.toString()+"@"+methodName+"@POS:");
//		if(!sm.hasActiveBody()){
//			sb.append("null");
//			return sb.toString();
//		}
//		UnitGraph g = new ExceptionalUnitGraph(sm.getActiveBody());
//	    Orderer<Unit> orderer = new PseudoTopologicalOrderer<Unit>();
//	    int cnt = 0;
//	    for (Unit u : orderer.newList(g, false)) {
//	    	cnt++;
//	    	if(stmt == (Stmt)u)
//	    		break;
//	    }
//	    sb.append(cnt);
//	    return sb.toString();
//	}
	
	public void addSensitiveUISource(Stmt stmt, IInfoflowCFG cfg){
		if(!allowSensitiveUISourceUpdate)
			return ;
		String sig = ToolSet.createStmtSignature(stmt, cfg);
		sensitiveUISource.add(sig);
	}
	
	public boolean isSensitiveUISource(Stmt stmt){
		String sig = ToolSet.createStmtSignature(stmt, null);
		boolean rs = sensitiveUISource.contains(sig);
		if(rs) NUDisplay.debug("isSensitiveUISource: "+stmt+" YES", null);
		else {
			if(stmt.containsInvokeExpr()){
				InvokeExpr ie = stmt.getInvokeExpr();
				if(ie.getMethod().getName().equals("findViewById"))
					rs = true;
			}
		}
		return rs;
	}
	
	public void addFieldID(SootField sf, Integer id){
		fieldIDMap.put(getFieldKey(sf), id);
	}
	
	public Integer getFieldID(SootField sf){
		return fieldIDMap.get(getFieldKey(sf));
	}
	public void addClassWithUnsolvedLayout(String clsName){
		this.classWithUnsolvedLayoutSet.add(clsName);
	}
	public Set<String> getClassWtihUnsolvedLayoutSet(){
		return this.classWithUnsolvedLayoutSet;
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
		String key = ToolSet.createStmtSignature(view, (IInfoflowCFG)cfg);
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
		String key = ToolSet.createStmtSignature(view, (IInfoflowCFG)cfg);
		return this.dynamicViewStmtIDMap.get(key);
	}
	
	public List<String> getDynamicViewTexts(Stmt view,  IInfoflowCFG cfg){
		return dynamicViewTextMap.get(ToolSet.createStmtSignature(view, cfg));
	}
	
	public void addViewID(Stmt stmt, BiDiInterproceduralCFG<Unit, SootMethod> icfg, Integer id){
		if(!stmt.containsInvokeExpr() || !stmt.getInvokeExpr().getMethod().getName().equals("findViewById")){
			NUDisplay.error("addViewID: stmt doesn't contain findViewById: "+stmt, null);
			return ;
		}
		SootMethod sm = icfg.getMethodOf(stmt);
		if(!sm.hasActiveBody()){
			NUDisplay.error("addViewID: stmt is not in active method: "+sm, null);
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
			NUDisplay.error("Error getViewID: stmt doesn't contain findViewById: "+stmt, null);
			return null;
		}
		SootMethod sm = icfg.getMethodOf(stmt);
		if(!sm.hasActiveBody()){
			NUDisplay.error("Error getViewID: stmt is not in active method: "+sm, null);
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