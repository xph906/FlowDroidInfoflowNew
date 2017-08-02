package soot.jimple.infoflow.nu;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import nu.NUDisplay;
import nu.NUSootConfig;
import heros.InterproceduralCFG;
//import nu.NUDisplay;
import soot.Local;
import soot.MethodOrMethodContext;
import soot.PatchingChain;
import soot.Scene;
import soot.SootField;
import soot.SootMethod;
import soot.Type;
import soot.Unit;
import soot.Value;
import soot.jimple.ArrayRef;
import soot.jimple.AssignStmt;
import soot.jimple.CastExpr;
import soot.jimple.Constant;
import soot.jimple.DefinitionStmt;
import soot.jimple.FieldRef;
import soot.jimple.IdentityStmt;
import soot.jimple.InstanceFieldRef;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.IntConstant;
import soot.jimple.InvokeExpr;
import soot.jimple.NewExpr;
import soot.jimple.ParameterRef;
import soot.jimple.Ref;
import soot.jimple.RetStmt;
import soot.jimple.ReturnStmt;
import soot.jimple.StaticFieldRef;
import soot.jimple.Stmt;
import soot.jimple.StringConstant;
import soot.jimple.ThisRef;
import soot.jimple.infoflow.results.ResultSinkInfo;
import soot.jimple.infoflow.results.ResultSourceInfo;
import soot.jimple.infoflow.solver.cfg.IInfoflowCFG;
import soot.jimple.infoflow.source.ISourceSinkManager;
import soot.jimple.internal.JimpleLocal;
import soot.jimple.toolkits.ide.icfg.BiDiInterproceduralCFG;
import soot.jimple.toolkits.scalar.ConstantPropagatorAndFolder;
import soot.tagkit.IntegerConstantValueTag;
import soot.tagkit.StringConstantValueTag;
import soot.tagkit.Tag;
import soot.toolkits.graph.ExceptionalUnitGraph;
import soot.toolkits.graph.Orderer;
import soot.toolkits.graph.PseudoTopologicalOrderer;
import soot.toolkits.graph.UnitGraph;
import soot.util.queue.QueueReader;

public class FlowPathSet {
	/*** Static Final Fields ***/
	static final String CALLBACK_LIST_FILE_NAME = "../soot-infoflow-android/AndroidCallbacks.txt";
	static final String SET_CONTENT_VIEW = "setContentView";
	static final String FIND_VIEW_BY_ID = "findViewById";
	static final String INTENT_PUT_SIGNATURE_STR = "android.content.Intent: android.content.Intent put";
	static final String BUNDLE_PUT_SIGNATURE_STR = "android.os.Bundle: void put";
	static final String PREFERENCE_PUT_SIGNATURE_STR = "android.content.SharedPreferences$Editor put";
	static final String FIND_VIEW_BY_ID_SIGNATURE_STR = "android.view.View findViewById(int)";
	static final String INTENT_GET_PATTERN = "android\\.content\\.Intent\\: (.)+get([A-Z][a-zA-Z0-9]+)?\\(";
	static final Pattern intentGetPattern = Pattern.compile(INTENT_GET_PATTERN);
	static final String BUNDLE_GET_PATTERN = "android\\.os\\.Bundle\\: (.)+get([A-Z][a-zA-Z0-9]+)?\\(";
	static final Pattern bundleGetPattern = Pattern.compile(BUNDLE_GET_PATTERN);
	static final String PREFERENCE_GET_PATTERN = "android\\.content\\.SharedPreferences\\: (.)+get[A-Z][a-zA-Z0-9]+\\(";
	static final Pattern preferenceGetPattern = Pattern.compile(PREFERENCE_GET_PATTERN);
	
	/*** Static Final Fields and Setters ***/
	static private IInfoflowCFG icfg ;
	static public void setCFG(IInfoflowCFG cfg){
		icfg = cfg;
	}
	static public IInfoflowCFG getCFG(){
		return icfg;
	}
	//TODO: another version of stmt signature is at ToolSet.
	//find a better one and use it instead.
	static public String getStmtSignatureForDynamicCombination(Stmt stmt, SootMethod sm){
//		if(icfg == null){
//			NUDisplay.error("icfg is null!"+stmt+"@"+sm.getSignature(), "getStmtSignatureForDynamicCombination");
//			return stmt.toString();
//		}
//		SootMethod sm = icfg.getMethodOf(stmt);
		if(sm == null){
			NUDisplay.error("sootmethod is null!"+stmt, "getStmtSignatureForDynamicCombination");
			return stmt.toString();
		}
		if(sm.hasActiveBody()){
			PatchingChain<Unit> units = sm.getActiveBody().getUnits();
			int cnt = 0;
			for(Unit unit : units){
				if(unit == stmt)
					return stmt.toString()+"@"+sm.getSignature()+"@"+cnt;
				cnt++;
			}
			NUDisplay.error("this stmt not exists!"+stmt+"@"+sm.getSignature(), "getStmtSignatureForDynamicCombination");
		}
		return stmt.toString()+"@"+sm.getSignature();
//		return ToolSet.createStmtSignatureWithMethod(stmt, sm);
	}
	
	/*** Methods to extract value from Stmts ***/
	static public Integer getViewIdFromStmt(Stmt stmt){
		if(stmt==null ) return null;
		if(!stmt.containsInvokeExpr() && !ToolSet.isDynamicWidgetOrDialogSource(stmt))
			return null;
		
		if(ToolSet.isDynamicWidgetOrDialogSource(stmt)){
			GlobalData gData = GlobalData.getInstance();
			Integer id = gData.getDynamicViewID(stmt, icfg);
			return id;
		}
		
		InvokeExpr ie = stmt.getInvokeExpr();
		SootMethod sm = ie.getMethod();
		if(sm.getName().equals(FIND_VIEW_BY_ID)){
			Value v = ie.getArg(0);
			if(v instanceof Constant){
				try{
					Integer id = Integer.valueOf(((Constant)v).toString());
					return id;
				}
				catch(Exception e){
					NUDisplay.error(FIND_VIEW_BY_ID+":"+e, "getViewIdFromStmt");
				}
			}
			else {
				GlobalData global = GlobalData.getInstance();
				Integer id = global.getViewID(stmt, icfg);
				return id;
			}
		}
		else if(sm.getName().equals(SET_CONTENT_VIEW)){
			try{
				Value v = stmt.getInvokeExpr().getArg(0);
				if(v instanceof Constant){
					Integer id = Integer.valueOf(((Constant)v).toString());
					return id;
				}
				else{
					SootMethod m = icfg.getMethodOf(stmt);
					GlobalData global = GlobalData.getInstance();
					Integer id = global.getLayoutID(m.getDeclaringClass().getName());
					return id;
				}
			}
			catch(Exception e){
				NUDisplay.error(SET_CONTENT_VIEW+":"+e, "getViewIdFromStmt");
			}
		}
		return null;
	}
	static public String getPreferenceKey(Stmt stmt){
		if(stmt==null || !stmt.containsInvokeExpr())
			return null;
		InvokeExpr ie = stmt.getInvokeExpr();
		SootMethod sm = ie.getMethod();
		if(!sm.getSignature().contains("SharedPreferences"))
			return null;
		if(sm.getName().equals("putBoolean") || 
			sm.getName().equals("putFloat") ||
			sm.getName().equals("putInt") ||
			sm.getName().equals("putLong") ||
			sm.getName().equals("putString") ||
			sm.getName().equals("getBoolean") || 
			sm.getName().equals("getFloat") ||
			sm.getName().equals("getInt") ||
			sm.getName().equals("getLong") ||
			sm.getName().equals("getString") ){
			Value v = ie.getArg(0);
			if(v instanceof Constant){
				try{
					Constant c = (Constant)v;
					return String.valueOf(c.toString());
				}
				catch(Exception e){
					NUDisplay.error(sm.getName() + e, "getPreferenceKey");
				}
			}
			else{
				String key = ToolSet.findLastResStringAssignmentAccurate(stmt, v, icfg, new HashSet<Stmt>());
				return key;
			}
		}
		return null;
	}
	static public String getIntentKey(Stmt stmt){
		if(stmt==null || !stmt.containsInvokeExpr())
			return null;
		InvokeExpr ie = stmt.getInvokeExpr();
		SootMethod sm = ie.getMethod();
		if(!sm.getDeclaringClass().getName().equals("android.content.Intent"))
			return null;
		if(sm.getParameterCount()<=0)
			return null;
		if(sm.getName().contains("get") || 
			sm.getName().contains("put")){
			Value v = ie.getArg(0);
			if(v instanceof Constant){
				try{
					Constant c = (Constant)v;
					return String.valueOf(c.toString());
				}
				catch(Exception e){
					NUDisplay.error("getIntentKey: " + e, "getIntentKey");
				}
			}
			else{
				String key = ToolSet.findLastResStringAssignmentAccurate(stmt, v, icfg, new HashSet<Stmt>());
				return key;
			}
		}
		return null;
	}
	static public String getBundleKey(Stmt stmt){
		if(stmt==null || !stmt.containsInvokeExpr())
			return null;
		InvokeExpr ie = stmt.getInvokeExpr();
		SootMethod sm = ie.getMethod();
		if(!sm.getDeclaringClass().getName().equals("android.os.Bundle"))
			return null;
		if(sm.getParameterCount()<=0)
			return null;
		if(sm.getName().contains("get") || 
			sm.getName().contains("put")){
			Value v = ie.getArg(0);
			if(v instanceof Constant){
				try{
					Constant c = (Constant)v;
					return String.valueOf(c.toString());
				}
				catch(Exception e){
					System.err.println("error getBundleKey: " + e+" //"+stmt);
				}
			}
			else{
				String key = ToolSet.findLastResStringAssignmentAccurate(stmt, v, icfg, new HashSet<Stmt>());
				return key;				
			}
		}
		return null;
	}
	
	/*** Instance Fields ***/
	private List<FlowPath> lst;
	
	/* Key: the FlowPath's id
	 * Value: a set of View ids associated with this flow. */
	private Map<Integer, Set<Integer>> viewFlowMap;
	
	/* Key: the FlowPath's id
	 * Value: a list of View's creation stmts associated with this flow. 
	 * Used for views created programmatically */
	private Map<Integer, Set<Stmt>> viewStmtFlowMap;
	
	/* Key: the event listener's type name (e.g., android.app.ActionBar$TabListener)
	 * Value: a list of stmts registering this listener.  */
	private Map<String, List<Stmt>> registryMap = null;
	
	/* Key: a list of listener's type name (e.g., android.app.ActionBar$TabListener) */
	private Set<String> callbackListenerSet = null;
	
	/* Key: a list of life cycle event names (e.g., onCreate) */
	private Set<String> lifeCycleEventListenerSet = null;
	
	/* Key: activity class name
	 * Value: a set of corresponding Layout IDs */
	private Map<String, Set<Integer>> activityLayoutMap; 
	
	/* Used for correlating view and flows that saved in
	 * preference, intent and bundle.
	 * e.g., putBoolean() -> Set<Stmt>(findViewById(...)) */
	private Map<Stmt, Set<Stmt>> preferenceValue2ViewMap; 
	private Map<String, Set<Integer>> preferenceKey2ViewIDMap;
	private Map<Stmt, Set<Stmt>> intentValue2ViewMap;
	private Map<String, Set<Integer>> intentKey2ViewIDMap;
	private Map<Stmt, Set<Stmt>> bundleValue2ViewMap;
	private Map<String, Set<Integer>> bundleKey2ViewIDMap;
	
	/* Used for inter-component analysis. */
	private Map<String, Set<FlowPath>> intentSinkMap;
	private Map<String, Set<FlowPath>> intentSourceMap;
	private Map<String, Set<FlowPath>> bundleSinkMap;
	private Map<String, Set<FlowPath>> bundleSourceMap;
	private Map<String, Set<FlowPath>> preferenceSinkMap;
	private Map<String, Set<FlowPath>> preferenceSourceMap;
	
	private ISourceSinkManager sourceSinkMgr;
	
	/* Used to ensure added flows being unique. */
	private Set<String> addedFlowSet;
	
	public FlowPathSet(){
		this.lst = new ArrayList<FlowPath>();
		this.callbackListenerSet = loadAndroidCallBackListeners();
		this.lifeCycleEventListenerSet = new HashSet<String>();
		viewFlowMap = new HashMap<Integer, Set<Integer>>();
		/* Key:
		 *   1. For UI event, the key is the listener's type;
		 *   2. For life cycle event (e.g., onCreate), the key is composed 
		 *      of the method's name and declaring class (the method's signature).
		 * Value:
		 *   Value would be a list of statements calling this method. */
		this.registryMap = new HashMap<String, List<Stmt>>();
		this.activityLayoutMap = new HashMap<String, Set<Integer>>();
		
		buildLifeCycleEventMap();
		buildEventRegisteryMapAndActivityLayoutMap();
		
		
		viewStmtFlowMap = new HashMap<Integer, Set<Stmt>>();
		preferenceValue2ViewMap = new HashMap<Stmt, Set<Stmt>>();
		preferenceKey2ViewIDMap = new HashMap<String, Set<Integer>>();
		
		intentValue2ViewMap = new HashMap<Stmt, Set<Stmt>>();
		intentKey2ViewIDMap = new HashMap<String, Set<Integer>>();
		
		bundleValue2ViewMap = new HashMap<Stmt, Set<Stmt>>();
		bundleKey2ViewIDMap = new HashMap<String, Set<Integer>>();
		
		intentSinkMap = new HashMap<String, Set<FlowPath>>();
		intentSourceMap = new HashMap<String, Set<FlowPath>>();
		bundleSinkMap = new HashMap<String, Set<FlowPath>>();
		bundleSourceMap = new HashMap<String, Set<FlowPath>>();
		preferenceSinkMap = new HashMap<String, Set<FlowPath>>();
		preferenceSourceMap = new HashMap<String, Set<FlowPath>>();
		
		addedFlowSet = new HashSet<String>();
	}
	
	/*** Public Methods ***/
	public void addFlowPath(FlowPath fp){
		if(fp.getId() != -1){
			NUDisplay.error("failed to addFlowPath: the path has been added already.", "addFlowPath");
			return ;
		}
		if(addedFlowSet.contains(fp.getSignature())){
			NUDisplay.error("failed to addFlowPath: the path has been added already.", "addFlowPath");
			return ;
		}
		//1. If a flow's source is findViewById, we don't consider it as a information leakage flow,
		//unless findViewById is a passpword edit text.
		//2. The reason we put findViewById in the source is that it provides a way to correlate views 
		//and flows.
		//3. Preference, Intent and Bundle are used to check if any views saved in them, so they could
		//be used to correlate views and flows.
		if(fp.getSource().getSource().toString().contains(FIND_VIEW_BY_ID_SIGNATURE_STR) ||
				ToolSet.isDynamicWidgetOrDialogSource(fp.getSource().getSource())){
			if(fp.getSink().getSink().toString().contains(PREFERENCE_PUT_SIGNATURE_STR)){
				//View to Preference Correlation
				Stmt src = fp.getSource().getSource();
				Stmt sink = fp.getSink().getSink();
				String key = getPreferenceKey(sink);
				Integer viewID = getViewIdFromStmt(src);
				if(preferenceValue2ViewMap.containsKey(sink))
					preferenceValue2ViewMap.get(sink).add(src);
				else{
					Set<Stmt> set = new HashSet<Stmt>();
					set.add(src);
					preferenceValue2ViewMap.put(sink, set);
				}
				
				if(key!=null && viewID!=null){
					if(preferenceKey2ViewIDMap.containsKey(key))
						preferenceKey2ViewIDMap.get(key).add(viewID);
					else{
						Set<Integer> set = new HashSet<Integer>();
						set.add(viewID);
						preferenceKey2ViewIDMap.put(key, set);
					}
				}
			}
			else if(fp.getSink().getSink().toString().contains(INTENT_PUT_SIGNATURE_STR)){
				Stmt src = fp.getSource().getSource();
				Stmt sink = fp.getSink().getSink();
				String key = getIntentKey(sink);
				Integer viewID = getViewIdFromStmt(src);
				if(intentValue2ViewMap.containsKey(sink))
					intentValue2ViewMap.get(sink).add(src);
				else{
					Set<Stmt> set = new HashSet<Stmt>();
					set.add(src);
					intentValue2ViewMap.put(sink, set);
				}
				if(key!=null && viewID!=null){
					if(intentKey2ViewIDMap.containsKey(key))
						intentKey2ViewIDMap.get(key).add(viewID);
					else{
						Set<Integer> set = new HashSet<Integer>();
						set.add(viewID);
						intentKey2ViewIDMap.put(key, set);
					}
				}
			}
			else if(fp.getSink().getSink().toString().contains(BUNDLE_PUT_SIGNATURE_STR)){
				Stmt src = fp.getSource().getSource();
				Stmt sink = fp.getSink().getSink();
				String key = getBundleKey(sink);
				Integer viewID = getViewIdFromStmt(src);
				if(bundleValue2ViewMap.containsKey(sink))
					bundleValue2ViewMap.get(sink).add(src);
				else{
					Set<Stmt> set = new HashSet<Stmt>();
					set.add(src);
					bundleValue2ViewMap.put(sink, set);
				}
				if(key!=null && viewID!=null){
					if(bundleKey2ViewIDMap.containsKey(key))
						bundleKey2ViewIDMap.get(key).add(viewID);
					else{
						Set<Integer> set = new HashSet<Integer>();
						set.add(viewID);
						bundleKey2ViewIDMap.put(key, set);
					}
				}
			}
			
			GlobalData gData = GlobalData.getInstance();
			if(!gData.isSensitiveUISource(fp.getSource().getSource()))
				return;
		}//source is findViewByID.
		
		NUSootConfig nuConfig = NUSootConfig.getInstance();
		if(nuConfig.isInterComponentAnalysisEnabled() && handleInterComponentHelper(fp))
			return ;
		
		//get rid of all non-method source
		if(!fp.getSource().getSource().containsInvokeExpr()){
			NUDisplay.debug("remove flow: "+fp.getSignature(), "addFlowPath");
			return ;
		}
		
		//get rid of semi flows.
		SootMethod sm = fp.getSource().getSource().getInvokeExpr().getMethod();
		String clsName = sm.getDeclaringClass().getName();
		if(clsName.contains("android.content.Intent") || 
				clsName.contains("android.os.Bundle") ||
				clsName.contains("SharedPreferences"))
			return ;
		sm = fp.getSink().getSink().getInvokeExpr().getMethod();
		clsName = sm.getDeclaringClass().getName();
		if(clsName.contains("android.content.Intent") || 
				clsName.contains("android.os.Bundle") ||
				clsName.contains("SharedPreferences"))
			return ;
		
		//For regular flows, we add them into list.
		fp.setId(lst.size());
		lst.add(fp);
		addedFlowSet.add(fp.getSignature());
	}
	
	
	public void updateViewsInPaths(){
		if(sourceSinkMgr == null){
			NUDisplay.error("sourceSinkManager is not set.","updateViewsInPaths");
			return ;
		}
		for(FlowPath fp : lst){
			fp.getId();
			List<Integer> viewIDs = fp.findViewsInPaths(sourceSinkMgr);
			if(viewIDs == null) continue;
			for(Integer id : viewIDs){
				if(id == null) continue;
				addViewFlowMapping(fp.getId(), id);	
			}
		}
	}
	
	public void handleInterComponent(){
		for(String key : intentSinkMap.keySet()){
			Set<FlowPath> sources = intentSinkMap.get(key);
			Set<FlowPath> sinks = intentSourceMap.get(key);
			if(sinks == null) continue;
			for(FlowPath source : sources){
				for(FlowPath sink : sinks){
					FlowPath fp = new FlowPath(source, sink);
					fp.setId(lst.size());
					lst.add(fp);
					addedFlowSet.add(fp.getSignature());
				}
			}
		}
		for(String key : bundleSinkMap.keySet()){
			Set<FlowPath> sources = bundleSinkMap.get(key);
			Set<FlowPath> sinks = bundleSourceMap.get(key);
			if(sinks == null) continue;
			for(FlowPath source : sources){
				for(FlowPath sink : sinks){
					FlowPath fp = new FlowPath(source, sink);
					fp.setId(lst.size());
					lst.add(fp);
					addedFlowSet.add(fp.getSignature());
				}
			}
		}
		for(String key : preferenceSinkMap.keySet()){
			Set<FlowPath> sources = preferenceSinkMap.get(key);
			Set<FlowPath> sinks = preferenceSourceMap.get(key);
			if(sinks == null) continue;
			for(FlowPath source : sources){
				for(FlowPath sink : sinks){
					FlowPath fp = new FlowPath(source, sink);
					fp.setId(lst.size());
					lst.add(fp);
					addedFlowSet.add(fp.getSignature());
				}
			}
		}
	}
	
	public List<Integer> findFlowPath(Stmt s, InterproceduralCFG<Unit, SootMethod> icfg){
		 List<Integer> rs = new ArrayList<Integer>();
		 for(int i=0; i<lst.size(); i++){
			 FlowPath fp = lst.get(i);
			 if(fp.findStmtFromFlowPath(s, icfg) != null)
				 rs.add(i);
		 }
		 return rs;
	}
	
	public void updateXMLEventListener(Map<String, Set<Integer>> xmlEventHandler2ViewIds){
		for(int i=0; i<lst.size(); i++){
			FlowPath fp = lst.get(i);
			Set<String> methods = fp.getAllTrigerMethodSet();
			for(String method : methods){
				if(xmlEventHandler2ViewIds.containsKey(method)){
					Set<Integer> views = xmlEventHandler2ViewIds.get(method);
					for(Integer viewID : views)
						addViewFlowMapping(i, viewID);
				}
			}
		}
	}
	
	public void addViewFlowMapping(int flowId, int viewId){
		
		if(viewFlowMap.containsKey(flowId)){
			viewFlowMap.get(flowId).add(viewId);
		}
		else{
			Set<Integer> viewids = new HashSet<Integer>();
			viewFlowMap.put(flowId, viewids);
			viewids.add(viewId);
		}
	}
	
	public void addViewFlowMapping(int flowId, Stmt viewStmt){
		if(viewStmtFlowMap.containsKey(flowId)){
			viewStmtFlowMap.get(flowId).add(viewStmt);
		}
		else{
			Set<Stmt> viewstmts = new HashSet<Stmt>();
			viewStmtFlowMap.put(flowId, viewstmts);
			viewstmts.add(viewStmt);
		}
	}
	
	/* Debugging purpose */
	public void displayFlowPaths(){
		NUDisplay.debug("Display all the flowpath:", null);
		for(FlowPath fp : lst){
			NUDisplay.debug("Flow:"+fp.getSource()+" => "+fp.getSink(), null);
		}
	}
	
	public String getClassNameFromLayoutId(Integer id){
		if(id == null) return null;
		for(String clsName : activityLayoutMap.keySet()){
			Set<Integer> ids = activityLayoutMap.get(clsName);
			if(ids != null){
				for(Integer cid : ids)
					if(cid.equals(id))
						return clsName;
			}
		}
		return null;
	}

	/*** Getters ***/
	public ISourceSinkManager getSourceSinkMgr() {
		return sourceSinkMgr;
	}
	public Map<String, Set<Integer>> getIntentKey2ViewIDMap() {
		return intentKey2ViewIDMap;
	}
	public Map<String, Set<Integer>> getBundleKey2ViewIDMap() {
		return bundleKey2ViewIDMap;
	}
	public Map<String, List<Stmt>> getRegistryMap() {
		return registryMap;
	}
	public Set<String> getLifeCycleEventListenerSet() {
		return lifeCycleEventListenerSet;
	}
	public Map<String, Set<Integer>> getActivityLayoutMap() {
		return activityLayoutMap;
	}
	public Map<Integer, Set<Integer>> getViewFlowMap() {
		return viewFlowMap;
	}
	public Map<Integer, Set<Stmt>> getViewStmtFlowMap(){
		return viewStmtFlowMap;
	}
	public Map<String, Set<Integer>> getPreferenceKey2ViewIDMap() {
		return preferenceKey2ViewIDMap;
	}
	public List<FlowPath> getLst() {
		return lst;
	}
	
	/*** Setters ***/
	public void setSourceSinkMgr(ISourceSinkManager sourceSinkMgr) {
		this.sourceSinkMgr = sourceSinkMgr;
	}
	public void setLst(List<FlowPath> lst) {
		this.lst = lst;
	}
	/*** Private inner methods ***/
	
	private void buildEventRegisteryMapAndActivityLayoutMap(){
		for (QueueReader<MethodOrMethodContext> rdr =
				Scene.v().getReachableMethods().listener(); rdr.hasNext(); ) {
			SootMethod m = rdr.next().method();
			if(!m.hasActiveBody())
				continue;
			UnitGraph g = new ExceptionalUnitGraph(m.getActiveBody());
		    Orderer<Unit> orderer = new PseudoTopologicalOrderer<Unit>();
		    for (Unit u : orderer.newList(g, false)) {
		    	Stmt s = (Stmt)u;
		    	if(s.containsInvokeExpr()){
		    		InvokeExpr expr = s.getInvokeExpr();
		    		SootMethod invokedM = expr.getMethod();
		    		for(int i=0; i<invokedM.getParameterCount(); i++){
		    			Type type = invokedM.getParameterType(i);
		    			if(callbackListenerSet.contains(type.getEscapedName()) ){
		    				Value arg = expr.getArg(i);
		    				String argType = arg.getType().toString();
		    				if(registryMap.containsKey(argType))
		    					registryMap.get(argType).add(s);
		    				else{
		    					List<Stmt> lst = new ArrayList<Stmt>();
		    					lst.add(s);
		    					registryMap.put(argType, lst);
		    				}
		    			}
		    			
		    		}
		    	}
		    	
		    	if(s.containsInvokeExpr()){
		    		InvokeExpr expr = s.getInvokeExpr();
		    		SootMethod invokedM = expr.getMethod();
		    			
		    		if(lifeCycleEventListenerSet.contains(invokedM.getName())){
		    			String sig = invokedM.getSignature();
		    			if(registryMap.containsKey(sig))
	    					registryMap.get(sig).add(s);
	    				else{
	    					List<Stmt> lst = new ArrayList<Stmt>();
	    					lst.add(s);
	    					registryMap.put(sig, lst);
	    				}
		    		}
		    		else if(invokedM.getName().equals(SET_CONTENT_VIEW)){
		    			try{
		    				Value v = s.getInvokeExpr().getArg(0);
		    				if(v instanceof Constant){
		    					Integer id = Integer.valueOf(((Constant)v).toString());
		    					String key = m.getDeclaringClass().getName();
		    					if(activityLayoutMap.containsKey(key)){
		    						activityLayoutMap.get(key).add(id);
		    					}
		    					else {
		    						Set<Integer> set = new HashSet<Integer>();
		    						set.add(id);
		    						activityLayoutMap.put(key, set);
		    					}
		    				}
		    				else{
		    					String key = m.getDeclaringClass().getName();
		    					Integer id = getViewIdFromStmt(s);
		    					if(id != null){
		    						if(activityLayoutMap.containsKey(key)){
			    						activityLayoutMap.get(key).add(id);
			    					}
			    					else {
			    						Set<Integer> set = new HashSet<Integer>();
			    						set.add(id);
			    						activityLayoutMap.put(key, set);
			    					}	
		    					}
		    				}
		    			}
		    			catch(Exception e){
		    				NUDisplay.error(e.toString(),"buildEventRegisteryMapAndActivityLayoutMap");
		    			}
		    		}
		    	}
		    }
		}
		
		for(String cls : activityLayoutMap.keySet()){
			Set<Integer> set = activityLayoutMap.get(cls);
			for(Integer id : set){
				NUDisplay.debug("Display LAYOUT MAP:"+cls+" => "+id, null);
			}
		}
		for(String listenerClsName : registryMap.keySet()){
			List<Stmt> list = registryMap.get(listenerClsName);
			for(Stmt stmt : list){
				NUDisplay.debug("Display Registry Map:"+listenerClsName+" => "+stmt, null);
			}
		}
		
	}
	
	private void buildLifeCycleEventMap(){
		this.lifeCycleEventListenerSet.add("onCreate");
		this.lifeCycleEventListenerSet.add("onPause");
		this.lifeCycleEventListenerSet.add("onStart");
		this.lifeCycleEventListenerSet.add("onResume");
		this.lifeCycleEventListenerSet.add("onRestart");
		this.lifeCycleEventListenerSet.add("onStop");
		this.lifeCycleEventListenerSet.add("onDestroy");	
	}
	
	private boolean isRealSource(Stmt source){
		Matcher intentGetMatcher = intentGetPattern.matcher(source.toString());
		if(intentGetMatcher.find())
			return false; //this is intent get.
		
		Matcher bundleGetMatcher = bundleGetPattern.matcher(source.toString());
		if (bundleGetMatcher.find())
			return false; //this is bundle get
		
		Matcher preferenceGetMatcher = preferenceGetPattern.matcher(source.toString());
		if(preferenceGetMatcher.find()) //preference get
			return false; 
		
		if(source.toString().contains(FIND_VIEW_BY_ID_SIGNATURE_STR)){
			 //if findViewById is password field, it's a real source
			GlobalData gd = GlobalData.getInstance();
			if(!gd.isSensitiveUISource(source))
				return false;
		}
		
		return true;
	}
	
	private boolean isRealSink(Stmt sink){
		if(sink.toString().contains(INTENT_PUT_SIGNATURE_STR))
			return false;
		if(sink.toString().contains(BUNDLE_PUT_SIGNATURE_STR))
			return false;
		if(sink.toString().contains(PREFERENCE_PUT_SIGNATURE_STR))
			return false;
		return true;
	}
	
	@SuppressWarnings("resource")
	private Set<String> loadAndroidCallBackListeners(){
		Set<String> androidCallbacks = new HashSet<String>();
		BufferedReader rdr = null;
		try {
			String fileName = CALLBACK_LIST_FILE_NAME;
			if (!new File(fileName).exists()) {
				fileName = "../soot-infoflow-android/AndroidCallbacks.txt";
				if (!new File(fileName).exists()){
					fileName = "AndroidCallbacks.txt";
					if (!new File(fileName).exists())
						throw new RuntimeException("Callback definition file not found");
				}
			}
			rdr = new BufferedReader(new FileReader(fileName));
			String line;
			while ((line = rdr.readLine()) != null)
				if (!line.isEmpty())
					androidCallbacks.add(line);
		}
		catch(Exception e){
			NUDisplay.error("failed to read callback file","loadAndroidCallBackListeners");
			System.exit(1);
		}
		
		return androidCallbacks;
	}
	
	/* This method is called in void addFlowPath(FlowPath) method.
	 * If inter-component analysis is enabled, it will store specific 
	 * semi-flow information.
	 * It returns true if it captures one semi-flow.
	 * Otherwise, it returns false*/
	private boolean handleInterComponentHelper(FlowPath fp){
		//Now source is guaranteed not to be non-password findViewById
		//CASE: sink is Intent put and source contains sensitive data.
		if(fp.getSink().getSink().toString().contains(INTENT_PUT_SIGNATURE_STR)){
			//sensitive_data stored to intent
			//store the information to intentSinkMap
			if(isRealSource(fp.getSource().getSource()) ){
				Stmt sink = fp.getSink().getSink();
				String key = getIntentKey(sink);
				if(key != null){
					NUDisplay.debug("NULIST: Semi-flow: Data->IntentGet:"+fp.getSource().getSource(), 
							"handleInterComponentHelper");
					if(intentSinkMap.containsKey(key))
						intentSinkMap.get(key).add(fp);
					else{
						Set<FlowPath> tmp = new HashSet<FlowPath>();
						intentSinkMap.put(key, tmp);
						tmp.add(fp);
					}
				}
			}
			
			return true;
		}
		
		//CASE: source is Intent get and sink is real sink
		Matcher matcher = intentGetPattern.matcher(fp.getSource().getSource().toString());
		if(matcher.find()){ //source is intent get and sink is not intent put
			//data extracted from intent is sent out
			//store the information to intentSourceMap.
			if(isRealSink(fp.getSink().getSink())){
				Stmt source = fp.getSource().getSource();
				String key = getIntentKey(source);
				if(key != null){
					NUDisplay.debug("NULIST: Semi-flow: IntentGet->Sink:"+fp.getSink().getSink(), 
							"handleInterComponentHelper");
					if(intentSourceMap.containsKey(key))
						intentSourceMap.get(key).add(fp);
					else{
						Set<FlowPath> tmp = new HashSet<FlowPath>();
						intentSourceMap.put(key, tmp);
						tmp.add(fp);
					}
				}
			}
			return true;
		}
		
		//CASE: sink is Bundle put and source contains sensitive data
		if(fp.getSink().getSink().toString().contains(BUNDLE_PUT_SIGNATURE_STR)){
			if(isRealSource(fp.getSource().getSource())){
				//TODO: store the sensitive source data to bundleSinkMap
				Stmt sink = fp.getSink().getSink();
				String key = getBundleKey(sink);
				if(key != null){
					NUDisplay.debug("NULIST: Semi-flow: Data->BundlPut:"+fp.getSource().getSource(),
							"handleInterComponentHelper");
					if(bundleSinkMap.containsKey(key))
						bundleSinkMap.get(key).add(fp);
					else{
						Set<FlowPath> tmp = new HashSet<FlowPath>();
						bundleSinkMap.put(key, tmp);
						tmp.add(fp);
					}
				}
			}
			return true;
		}
		
		//CASE: source is Bundle get and sink is real sink
		matcher = bundleGetPattern.matcher(fp.getSource().getSource().toString());
		NUDisplay.debug("BundleGet->Sink:"+fp.getSource().getSource()+" --"+fp.getSink().getSink(),
				"handleInterComponentHelper");
		if(matcher.find()){
			if(isRealSink(fp.getSink().getSink())){
				Stmt source = fp.getSource().getSource();
				String key = getBundleKey(source);
				if(key != null){
					NUDisplay.debug("NULIST: Semi-flow: BundleGet->Sink:"+fp.getSource().getSource(),
							"handleInterComponentHelper");
					if(bundleSourceMap.containsKey(key))
						bundleSourceMap.get(key).add(fp);
					else{
						Set<FlowPath> tmp = new HashSet<FlowPath>();
						bundleSourceMap.put(key, tmp);
						tmp.add(fp);
					}
				}
			}
			return true;
		}
		//CASE: sink is Preference put and source contains sensitive data
		if(fp.getSink().getSink().toString().contains(PREFERENCE_PUT_SIGNATURE_STR)){
			if(isRealSource(fp.getSource().getSource())){
				Stmt sink = fp.getSink().getSink();
				String key = getPreferenceKey(sink);
				if(key != null){
					NUDisplay.debug("NULIST: Semi-flow: Data->PreferencePut:"+fp.getSource().getSource(),
							"handleInterComponentHelper");
					if(preferenceSinkMap.containsKey(key))
						preferenceSinkMap.get(key).add(fp);
					else{
						Set<FlowPath> tmp = new HashSet<FlowPath>();
						preferenceSinkMap.put(key, tmp);
						tmp.add(fp);
					}
				}
			}
			return true;
		}
		//CASE: source is Preference get and sink is real sink
		matcher = preferenceGetPattern.matcher(fp.getSource().getSource().toString());
		if(matcher.find()){
			if(isRealSink(fp.getSink().getSink())){
				Stmt source = fp.getSource().getSource();
				String key = getBundleKey(source);
				if(key != null){
					NUDisplay.debug("NULIST: Semi-flow: PreferenceGet->Sink:"+fp.getSource().getSource(),
							"handleInterComponentHelper");
					if(preferenceSourceMap.containsKey(key))
						preferenceSourceMap.get(key).add(fp);
					else{
						Set<FlowPath> tmp = new HashSet<FlowPath>();
						preferenceSourceMap.put(key, tmp);
						tmp.add(fp);
					}
				}
			}
			return true;
		}
		return false;
	}
	
}
