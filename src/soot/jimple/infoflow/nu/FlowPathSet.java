package soot.jimple.infoflow.nu;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import heros.InterproceduralCFG;
import nu.NUDisplay;
import soot.Local;
import soot.MethodOrMethodContext;
import soot.Scene;
import soot.SootField;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.jimple.AssignStmt;
import soot.jimple.CastExpr;
import soot.jimple.Constant;
import soot.jimple.FieldRef;
import soot.jimple.IdentityStmt;
import soot.jimple.IntConstant;
import soot.jimple.InvokeExpr;
import soot.jimple.ParameterRef;
import soot.jimple.StaticFieldRef;
import soot.jimple.Stmt;
import soot.jimple.StringConstant;
import soot.jimple.infoflow.results.ResultSinkInfo;
import soot.jimple.infoflow.results.ResultSourceInfo;
import soot.jimple.infoflow.solver.cfg.IInfoflowCFG;
import soot.jimple.toolkits.ide.icfg.BiDiInterproceduralCFG;
import soot.jimple.toolkits.scalar.ConstantPropagatorAndFolder;
import soot.tagkit.StringConstantValueTag;
import soot.tagkit.Tag;
import soot.toolkits.graph.ExceptionalUnitGraph;
import soot.toolkits.graph.Orderer;
import soot.toolkits.graph.PseudoTopologicalOrderer;
import soot.toolkits.graph.UnitGraph;
import soot.util.queue.QueueReader;

public class FlowPathSet {
	static final String SET_CONTENT_VIEW = "setContentView";
	static final String FIND_VIEW_BY_UD = "findViewById";
	static final String INTENT_PUT_SIGNATURE_STR = "android.content.Intent: android.content.Intent put";
	static final String BUNDLE_PUT_SIGNATURE_STR = "android.os.Bundle: void put";
	static final String PREFERENCE_PUT_SIGNATURE_STR = "android.content.SharedPreferences$Editor put";
	static final String FIND_VIEW_BY_ID_SIGNATURE_STR = "android.view.View findViewById(int)";
	
	static final String INTENT_GET_PATTERN = "android\\.content\\.Intent\\: (.)+get[A-Z][a-zA-Z0-9]+\\(";
	static final Pattern intentGetPattern = Pattern.compile(INTENT_GET_PATTERN);
	
	static final String BUNDLE_GET_PATTERN = "android\\.os\\.Bundle\\: (.)+get[A-Z][a-zA-Z0-9]+\\(";
	static final Pattern bundleGetPattern = Pattern.compile(BUNDLE_GET_PATTERN);
	
	//android.content.SharedPreferences: boolean getBoolean(java.lang.String,boolean)
	static final String PREFERENCE_GET_PATTERN = "android\\.content\\.SharedPreferences\\: (.)+get[A-Z][a-zA-Z0-9]+\\(";
	static final Pattern preferenceGetPattern = Pattern.compile(PREFERENCE_GET_PATTERN);
	//final AccessPathBasedSourceSinkManager 
	
	static private IInfoflowCFG icfg ;
	static public void setCFG(IInfoflowCFG cfg){
		icfg = cfg;
	}
	
	static public Integer getViewIdFromStmt(Stmt stmt){
		if(stmt==null || !stmt.containsInvokeExpr())
			return null;
		InvokeExpr ie = stmt.getInvokeExpr();
		SootMethod sm = ie.getMethod();
		//TODO: add setContentView
		if(sm.getName().equals(FIND_VIEW_BY_UD)){
			//TODO: handle if findViewById is not a constant
			Value v = ie.getArg(0);
			if(v instanceof Constant){
				try{
					Constant c = (Constant)v;
					Integer intVal = Integer.valueOf(c.toString());
					return intVal;
				}
				catch(Exception e){
					System.err.println("getViewIdFromStmt: " + e);
				}
			}
			else {
				GlobalData global = GlobalData.getInstance();
				Integer id = global.getViewID(stmt, icfg);
				if(id != null){
					NUDisplay.debug("getViewIdFromStmt can find ViewID[findViewById]:"+stmt, icfg.getMethodOf(stmt).getSignature());
					return id;
				}
				else {
					NUDisplay.debug("getViewIdFromStmt cannot find ViewID[findViewById]:"+stmt, icfg.getMethodOf(stmt).getSignature());
				}
			}
		}
		else if(sm.getName().equals(SET_CONTENT_VIEW)){
			try{
				Value v = stmt.getInvokeExpr().getArg(0);
				//TODO: handle when arg is not CONSTANT
				if(v instanceof Constant){
					//System.out.println("DEBUG7: "+s);
					Integer id = Integer.valueOf(((Constant)v).toString());
					return id;
				}
				else{
					SootMethod m = icfg.getMethodOf(stmt);
					GlobalData global = GlobalData.getInstance();
					Integer id = global.getLayoutID(m.getDeclaringClass().getName());
					if(id == null){
						NUDisplay.debug("getViewIdFromStmt cannot find ViewID[setContentView]:"+stmt, icfg.getMethodOf(stmt).getSignature());
					}
					else{
						NUDisplay.debug("getViewIdFromStmt can find ViewID[setContentView]:"+stmt, icfg.getMethodOf(stmt).getSignature());
					}
					return id;
				}
			}
			catch(Exception e){
				System.err.println("NULIST: error: buildEventRegisteryMapAndActivityLayoutMap "+e.toString());
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
					System.err.println("error getPreferenceKey: " + e+" //"+stmt);
				}
			}
			else{
//				System.out.println("NULIST: Cannot find the key for preference (not constant):"+stmt);
				String key = findLastResStringAssignment(stmt, v, icfg, new HashSet<Stmt>());
				if(key == null){
					String cls = icfg.getMethodOf(stmt).getDeclaringClass().getName();
					NUDisplay.debug("findLastResStringAssignment cannot resolve key[getPreferenceKey]:"+stmt, icfg.getMethodOf(stmt).getName()+" Of "+cls);
				}
				else{
					NUDisplay.debug("findLastResStringAssignment can resolve key[getPreferenceKey]:"+stmt, null);
				}
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
					//System.out.println("DEBUGINTENT:"+c+" S:"+stmt);
					return String.valueOf(c.toString());
				}
				catch(Exception e){
					System.err.println("error getIntentKey: " + e+" //"+stmt);
				}
			}
			else{
//				System.out.println("NULIST: Cannot find the key for Intent (not constant):"+stmt);
				String key = findLastResStringAssignment(stmt, v, icfg, new HashSet<Stmt>());
				if(key == null){
					String cls = icfg.getMethodOf(stmt).getDeclaringClass().getName();
					NUDisplay.debug("findLastResStringAssignment cannot resolve key[getIntentKey]:"+stmt, 
							icfg.getMethodOf(stmt).getName()+" Of "+cls);
				}
				else{
					NUDisplay.debug("findLastResStringAssignment can resolve key[getIntentKey]:"+stmt, null);
				}
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
					//System.out.println("DEBUGBUNDLE:"+c+" S:"+stmt);
					return String.valueOf(c.toString());
				}
				catch(Exception e){
					System.err.println("error getBundleKey: " + e+" //"+stmt);
				}
			}
			else{
//				System.out.println("NULIST: Cannot find the key for Bundle (not constant):"+stmt);
				String key = findLastResStringAssignment(stmt, v, icfg, new HashSet<Stmt>());
				if(key == null){
					String cls = icfg.getMethodOf(stmt).getDeclaringClass().getName();
					NUDisplay.debug("findLastResStringAssignment cannot resolve key[getBundleKey]:"+stmt, 
							icfg.getMethodOf(stmt).getName()+" Of "+cls);
				}
				else{
					NUDisplay.debug("findLastResStringAssignment can resolve key[getBundleKey]:"+stmt, null);
				}
				return key;				
			}
		}
		return null;
	}
	
	
	private List<FlowPath> lst;
	/* Key: the FlowPath's id
	 * Value: a list of View Id associated with this flow. */
	private Map<Integer, Set<Integer>> viewFlowMap;
	private Map<String, String> eventListenerMap = null;
	private Set<String> lifeCycleEventListenerSet = null;
	private Map<String, List<Stmt>> registryMap = null;
	private Set<String> eventRegistryMethodSet = null;
	//activity class name -> set of Layout IDs
	private Map<String, Set<Integer>> activityLayoutMap; 
	private Set<String> addedFlowSet;
	
	private Map<Stmt, Set<Stmt>> preferenceValue2ViewMap; //e.g., putBoolean(...) -> Set<Stmt>(findViewById(...))
	private Map<String, Set<Integer>> preferenceKey2ViewIDMap;
	
	private Map<Stmt, Set<Stmt>> intentValue2ViewMap;
	private Map<String, Set<Integer>> intentKey2ViewIDMap;
	
	private Map<Stmt, Set<Stmt>> bundleValue2ViewMap;
	private Map<String, Set<Integer>> bundleKey2ViewIDMap;
	
	private Map<String, Set<FlowPath>> intentSinkMap;
	private Map<String, Set<FlowPath>> intentSourceMap;
	private Map<String, Set<FlowPath>> bundleSinkMap;
	private Map<String, Set<FlowPath>> bundleSourceMap;
	private Map<String, Set<FlowPath>> preferenceSinkMap;
	private Map<String, Set<FlowPath>> preferenceSourceMap;
	
	
	public Map<String, Set<Integer>> getIntentKey2ViewIDMap() {
		return intentKey2ViewIDMap;
	}

	public Map<String, Set<Integer>> getBundleKey2ViewIDMap() {
		return bundleKey2ViewIDMap;
	}

	public Map<Stmt, Set<Stmt>> getPreferenceValue2ViewMap() {
		return preferenceValue2ViewMap;
	}

	public Map<String, List<Stmt>> getRegistryMap() {
		return registryMap;
	}

	public Set<String> getEventRegistryMethodSet() {
		return eventRegistryMethodSet;
	}

	public Map<String, String> getEventListenerMap() {
		return eventListenerMap;
	}

	public Set<String> getLifeCycleEventListenerSet() {
		return lifeCycleEventListenerSet;
	}

	public FlowPathSet(){
		this.lst = new ArrayList<FlowPath>();
		

		this.lifeCycleEventListenerSet = new HashSet<String>();
		this.eventListenerMap = new HashMap<String, String>();
		/* Key:
		 *   1. For eventRer2 = virtualinvoke $r0.<com.android.insecurebankv2.LoginActivity: android.view.View findViewById(int)>(2131558527)gistry (e.g., setOnClickListener), the key is the 
		 *      listener's type;
		 *   2. For lifeCycleEventListener (e.g., onCreate), the key is composed 
		 *      of the method's name and declaring class (the method's signature).
		 * Value:
		 *   Value would be a list of statements calling this method.
		 * */
		this.registryMap = new HashMap<String, List<Stmt>>();
		this.activityLayoutMap = new HashMap<String, Set<Integer>>();
		
		buildEventListenerMap();
		this.eventRegistryMethodSet = new HashSet<String>(this.eventListenerMap.values());
		
		buildEventRegisteryMapAndActivityLayoutMap();
		viewFlowMap = new HashMap<Integer, Set<Integer>>();
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

	public void addFlowPath(FlowPath fp){
		if(fp.getId() != -1){
			System.out.println("NULIST: ERROR: failed to addFlowPath: the path has been added already.");
			return ;
		}
		if(addedFlowSet.contains(fp.getSignature())){
			System.out.println("NULIST: ERROR: failed to addFlowPath: the path has been added already2.");
			return ;
		}
		
		if(fp.getSource().getSource().toString().contains(FIND_VIEW_BY_ID_SIGNATURE_STR)){
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
					System.out.println("NULIST: View2Preference: Found one map: "+key+" => "+viewID);
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
				//View to Intent Correlation
				//System.out.println("NULIST: IntentSet: "+fp.getSink().getSink().toString());
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
					System.out.println("NULIST: View2Intent: Found one map: "+key+" => "+viewID);
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
				//View to Bundle Correlation
				//System.out.println("NULIST: BundleSet: "+fp.getSink().getSink().toString());
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
					System.out.println("NULIST: View2Bundle: Found one map: "+key+" => "+viewID);
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
		
		//The following is used for inter-component analysis
		//Now source is guaranteed not to be non-password findViewById
		//CASE: sink is Intent put and source contains sensitive data.
		if(fp.getSink().getSink().toString().contains(INTENT_PUT_SIGNATURE_STR)){
			//sensitive_data stored to intent
			//store the information to intentSinkMap
			if(isRealSource(fp.getSource().getSource()) ){
				Stmt sink = fp.getSink().getSink();
				String key = getIntentKey(sink);
				if(key != null){
					System.out.println("NULIST: Semi-flow: Data->IntentGet:"+fp.getSource().getSource());
					if(intentSinkMap.containsKey(key))
						intentSinkMap.get(key).add(fp);
					else{
						Set<FlowPath> tmp = new HashSet<FlowPath>();
						intentSinkMap.put(key, tmp);
						tmp.add(fp);
					}
				}
			}
			
			return ;
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
					System.out.println("NULIST: Semi-flow: IntentGet->Sink:"+fp.getSink().getSink());
					if(intentSourceMap.containsKey(key))
						intentSourceMap.get(key).add(fp);
					else{
						Set<FlowPath> tmp = new HashSet<FlowPath>();
						intentSourceMap.put(key, tmp);
						tmp.add(fp);
					}
				}
			}
			return ;
		}
		//CASE: sink is Bundle put and source contains sensitive data
		if(fp.getSink().getSink().toString().contains(BUNDLE_PUT_SIGNATURE_STR)){
//			System.out.println("NULIST: TODO: sink is Bundle put. "+fp.getSink().getSink());
//			System.out.println("  "+fp.getSource().getSource());
			if(isRealSource(fp.getSource().getSource())){
				//TODO: store the sensitive source data to bundleSinkMap
				Stmt sink = fp.getSink().getSink();
				String key = getBundleKey(sink);
				if(key != null){
					System.out.println("NULIST: Semi-flow: Data->BundlPut:"+fp.getSource().getSource());
					if(bundleSinkMap.containsKey(key))
						bundleSinkMap.get(key).add(fp);
					else{
						Set<FlowPath> tmp = new HashSet<FlowPath>();
						bundleSinkMap.put(key, tmp);
						tmp.add(fp);
					}
				}
			}
			return ;
		}
		//CASE: source is Bundle get and sink is real sink
		matcher = bundleGetPattern.matcher(fp.getSource().getSource().toString());
		if(matcher.find()){
//			System.out.println("NULIST: TODO: source is Bundle get. "+fp.getSource().getSource());
//			System.out.println("  "+fp.getSink().getSink());
			if(isRealSink(fp.getSink().getSink())){
				Stmt source = fp.getSource().getSource();
				String key = getBundleKey(source);
				if(key != null){
					System.out.println("NULIST: Semi-flow: BundleGet->Sink:"+fp.getSink().getSink());
					if(bundleSourceMap.containsKey(key))
						bundleSourceMap.get(key).add(fp);
					else{
						Set<FlowPath> tmp = new HashSet<FlowPath>();
						bundleSourceMap.put(key, tmp);
						tmp.add(fp);
					}
				}
			}
			return ;
		}
		//CASE: sink is Preference put and source contains sensitive data
		if(fp.getSink().getSink().toString().contains(PREFERENCE_PUT_SIGNATURE_STR)){
//			System.out.println("NULIST: TODO: sink is Preference put. "+fp.getSink().getSink());
//			System.out.println("  "+fp.getSource().getSource());
			if(isRealSource(fp.getSource().getSource())){
				//TODO: store the sensitive source data to preferenceSinkMap
				Stmt sink = fp.getSink().getSink();
				String key = getPreferenceKey(sink);
				if(key != null){
					System.out.println("NULIST: Semi-flow: Data->PreferencePut:"+fp.getSource().getSource());
					if(preferenceSinkMap.containsKey(key))
						preferenceSinkMap.get(key).add(fp);
					else{
						Set<FlowPath> tmp = new HashSet<FlowPath>();
						preferenceSinkMap.put(key, tmp);
						tmp.add(fp);
					}
				}
			}
			return ;
		}
		//CASE: source is Preference get and sink is real sink
		matcher = preferenceGetPattern.matcher(fp.getSource().getSource().toString());
		if(matcher.find()){
//			System.out.println("NULIST: TODO: source is Preference get. "+fp.getSource().getSource());
//			System.out.println("  "+fp.getSink().getSink());
			if(isRealSink(fp.getSink().getSink())){
				Stmt source = fp.getSource().getSource();
				String key = getBundleKey(source);
				if(key != null){
					System.out.println("NULIST: Semi-flow: PreferenceGet->Sink:"+fp.getSink().getSink());
					if(preferenceSourceMap.containsKey(key))
						preferenceSourceMap.get(key).add(fp);
					else{
						Set<FlowPath> tmp = new HashSet<FlowPath>();
						preferenceSourceMap.put(key, tmp);
						tmp.add(fp);
					}
				}
			}
			return ;
		}
		
		//For regular flows, we add them into list.
		fp.setId(lst.size());
		lst.add(fp);
		addedFlowSet.add(fp.getSignature());
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
	
	
	public void handleInterComponent(){
		for(String key : intentSinkMap.keySet()){
			Set<FlowPath> sources = intentSinkMap.get(key);
			Set<FlowPath> sinks = intentSourceMap.get(key);
			if(sinks == null) continue;
			for(FlowPath source : sources){
				for(FlowPath sink : sinks){
					FlowPath fp = new FlowPath(source, sink);
					System.out.println("INTERCOMPONENT ADD NEW FLOW 1: "+key+" FP:"+fp.getTag());
					fp.setId(lst.size());
					lst.add(fp);
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
					System.out.println("INTERCOMPONENT ADD NEW FLOW 2: "+key+" FP:"+fp.getTag());
					fp.setId(lst.size());
					lst.add(fp);
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
					System.out.println("INTERCOMPONENT ADD NEW FLOW 3: "+key+" FP:"+fp.getTag());
					fp.setId(lst.size());
					lst.add(fp);
				}
			}
		}
	}
	
	public Map<String, Set<Integer>> getPreferenceKey2ViewIDMap() {
		return preferenceKey2ViewIDMap;
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

	public List<FlowPath> getLst() {
		return lst;
	}

	public void setLst(List<FlowPath> lst) {
		this.lst = lst;
	}
	
	//TODO: might be not complete.
	private void buildEventListenerMap(){
		
		this.eventListenerMap.put("onClick", "setOnClickListener");
		this.eventListenerMap.put("onLongClick", "setOnLongClickListener");
		
		this.eventListenerMap.put("onFocusChange", "setOnFocusChangeListener");
		this.eventListenerMap.put("onFocusChanged", "setOnFocusChangeListener");
		
		this.eventListenerMap.put("onKey", "setOnKeyListener");
		this.eventListenerMap.put("onKeyDown", "setOnKeyListener");
		this.eventListenerMap.put("onKeyUp", "setOnKeyListener");
		
		this.eventListenerMap.put("onTouchEvent", "setOnTouchListener");
		this.eventListenerMap.put("onTouch", "setOnTouchListener");
		
		
		this.lifeCycleEventListenerSet.add("onCreate");
		this.lifeCycleEventListenerSet.add("onPause");
		this.lifeCycleEventListenerSet.add("onStart");
		this.lifeCycleEventListenerSet.add("onResume");
		this.lifeCycleEventListenerSet.add("onRestart");
		this.lifeCycleEventListenerSet.add("onStop");
		this.lifeCycleEventListenerSet.add("onDestroy");	
	}
	
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
		    		if(eventRegistryMethodSet.contains(invokedM.getName())){
		    			if(invokedM.getParameterCount() == 1){ //e.g., setOnClickListener
		    				Value arg = expr.getArg(0); 
		    				String type = arg.getType().toString();
		    				//System.out.println("NULIST RC:"+type+" //"+invokedM.getName());
		    				if(registryMap.containsKey(type))
		    					registryMap.get(type).add(s);
		    				else{
		    					List<Stmt> lst = new ArrayList<Stmt>();
		    					lst.add(s);
		    					registryMap.put(type, lst);
		    				}
		    				System.out.println("DEBUG4:"+type+" -> "+s);
		    			}
		    		}
		    		else if(lifeCycleEventListenerSet.contains(invokedM.getName())){
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
		    				//TODO: handle when arg is not CONSTANT
		    				if(v instanceof Constant){
		    					//System.out.println("DEBUG7: "+s);
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
//		    					GlobalData global = GlobalData.getInstance();
//		    					Integer id = global.getLayoutID(m.getDeclaringClass().getName());
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
		    				System.err.println("NULIST: error: buildEventRegisteryMapAndActivityLayoutMap "+e.toString());
		    			}
		    		}
		    	}
		    }
		}
		
		for(String cls : activityLayoutMap.keySet()){
			Set<Integer> set = activityLayoutMap.get(cls);
			for(Integer id : set){
				System.out.println("Display LAYOUT:"+cls+" => "+id);
			}
		}
	}
	
	public Map<String, Set<Integer>> getActivityLayoutMap() {
		return activityLayoutMap;
	}

	public Map<Integer, Set<Integer>> getViewFlowMap() {
		return viewFlowMap;
	}
	
	//This method is called
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
	
	public void displayFlowPaths(){
		System.out.println("Display all the flowpath:");
		for(FlowPath fp : lst){
			System.out.println("Flow:"+fp.getSource()+" => "+fp.getSink());
		}
	}
	
	private static String findLastResStringAssignment(Stmt stmt, Value target, 
			BiDiInterproceduralCFG<Unit, SootMethod> cfg, Set<Stmt> visited) {
		if(visited.contains(stmt)){
			return null;
		}
		visited.add(stmt);
		
		if(cfg == null) {
			System.err.println("Error: findLastResIDAssignment cfg is not set.");
			return null;
		}
		// If this is an assign statement, we need to check whether it changes
		// the variable we're looking for
		if (stmt instanceof AssignStmt) {
			AssignStmt assign = (AssignStmt) stmt;
			if (assign.getLeftOp() == target) {
				// ok, now find the new value from the right side
				if (assign.getRightOp() instanceof StringConstant) {
					return ((StringConstant) assign.getRightOp()).value;
				} 
				else if (assign.getRightOp() instanceof FieldRef) {
					SootField field = ((FieldRef) assign.getRightOp()).getField();
					for (Tag tag : field.getTags()){
						if (tag instanceof StringConstantValueTag){
							//System.out.println("This is an integerCOnstantValue");
							return ((StringConstantValueTag) tag).getStringValue();
						}
					}
					if(assign.getRightOp() instanceof StaticFieldRef){
						StaticFieldRef sfr = (StaticFieldRef)assign.getRightOp();
						target = assign.getRightOp();
					}
				} 
				else if(assign.getRightOp() instanceof Local){
					target = assign.getRightOp();
				}
				else if(assign.getRightOp() instanceof CastExpr){
					target = assign.getRightOp();
				}
				else if (assign.getRightOp() instanceof InvokeExpr) {
					System.out.println("NULIST: TODO: findLastResStringAssignment right invoke expr:"+assign.getRightOp());
					return null;
				}
			}
			
		}
		else if(stmt instanceof IdentityStmt){
			IdentityStmt is = (IdentityStmt)stmt;
			if(is.getLeftOp() == target){
				//System.out.println("From IdentityStmt: "+is);
				if(is.getRightOp() instanceof ParameterRef){
					ParameterRef right = (ParameterRef)(is.getRightOp());
					int idx = right.getIndex();
					Collection<Unit> callers = cfg.getCallersOf(cfg.getMethodOf(stmt));
					if(callers != null && callers.size()>0){
						for(Unit caller : callers){
							InvokeExpr ie = ((Stmt)caller).getInvokeExpr();
							if(idx >= ie.getArgCount()) continue;
							Value arg = ie.getArg(idx);
							if(arg instanceof StringConstant)
								return ((StringConstant) arg).value;
							else{
								String lastAssignment = findLastResStringAssignment((Stmt) caller, arg, cfg, visited);
								if (lastAssignment != null)
									return lastAssignment;
							}
						}
					}
				}
			}
		}

		// Continue the search upwards
		for (Unit pred : cfg.getPredsOf(stmt)) {
			if (!(pred instanceof Stmt))
				continue;
			String lastAssignment = findLastResStringAssignment((Stmt) pred, target, cfg, visited);
			if (lastAssignment != null)
				return lastAssignment;
		}
		return null;
	}
}
