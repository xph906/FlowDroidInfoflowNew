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

import heros.InterproceduralCFG;
//import nu.NUDisplay;
import soot.Local;
import soot.MethodOrMethodContext;
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
	static final String CALLBACK_LIST_FILE_NAME = "../soot-infoflow-android/AndroidCallbacks.txt";
	static final String SET_CONTENT_VIEW = "setContentView";
	static final String FIND_VIEW_BY_ID = "findViewById";
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
		if(stmt==null )
			return null;
		if(!stmt.containsInvokeExpr() && !isDynamicWidgetOrDialogSource(stmt))
			return null;
		else if(isDynamicWidgetOrDialogSource(stmt)){
			GlobalData gData = GlobalData.getInstance();
			Integer id = gData.getDynamicViewID(stmt, icfg);
			//System.out.println("DEBUG GETDYNAMICVIEWID:"+id);
			return id;
		}
		InvokeExpr ie = stmt.getInvokeExpr();
		SootMethod sm = ie.getMethod();
		//TODO: add setContentView
		if(sm.getName().equals(FIND_VIEW_BY_ID)){
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
//					NUDisplay.debug("getViewIdFromStmt can find ViewID[findViewById]:"+stmt, icfg.getMethodOf(stmt).getSignature());
					return id;
				}
				else {
//					NUDisplay.debug("getViewIdFromStmt cannot find ViewID[findViewById]:"+stmt, icfg.getMethodOf(stmt).getSignature());
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
//						NUDisplay.debug("getViewIdFromStmt cannot find ViewID[setContentView]:"+stmt, icfg.getMethodOf(stmt).getSignature());
					}
					else{
//						NUDisplay.debug("getViewIdFromStmt can find ViewID[setContentView]:"+stmt, icfg.getMethodOf(stmt).getSignature());
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
					//NUDisplay.debug("findLastResStringAssignment cannot resolve key[getPreferenceKey]:"+stmt, icfg.getMethodOf(stmt).getName()+" Of "+cls);
				}
				else{
					//NUDisplay.debug("findLastResStringAssignment can resolve key[getPreferenceKey]:"+stmt, null);
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
//					NUDisplay.debug("findLastResStringAssignment cannot resolve key[getIntentKey]:"+stmt, 
//							icfg.getMethodOf(stmt).getName()+" Of "+cls);
				}
				else{
//					NUDisplay.debug("findLastResStringAssignment can resolve key[getIntentKey]:"+stmt, null);
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
//					NUDisplay.debug("findLastResStringAssignment cannot resolve key[getBundleKey]:"+stmt, 
//							icfg.getMethodOf(stmt).getName()+" Of "+cls);
				}
				else{
//					NUDisplay.debug("findLastResStringAssignment can resolve key[getBundleKey]:"+stmt, null);
				}
				return key;				
			}
		}
		return null;
	}
	
	private ISourceSinkManager sourceSinkMgr;
	public ISourceSinkManager getSourceSinkMgr() {
		return sourceSinkMgr;
	}

	public void setSourceSinkMgr(ISourceSinkManager sourceSinkMgr) {
		this.sourceSinkMgr = sourceSinkMgr;
	}

	private List<FlowPath> lst;
	/* Key: the FlowPath's id
	 * Value: a list of View Id associated with this flow. */
	private Map<Integer, Set<Integer>> viewFlowMap;
	/* Key: the FlowPath's id
	 * Value: a list of View's creation stmt associated with this flow. 
	 *        Used for views created programmatically*/
	private Map<Integer, Set<Stmt>> viewStmtFlowMap;
	/*	Key: findViewById Stmt or new View or new Dialog Stmts.
	 *  Value: a set of texts associated with this view.
	 * */
	private Map<Stmt, Set<String>> dynamicTextMap;
	private Map<String, String> eventListenerMap = null;
	private Set<String> lifeCycleEventListenerSet = null;
	private Map<String, List<Stmt>> registryMap = null;
	private Set<String> eventRegistryMethodSet = null;
	
	private Set<String> callbackListenerSet = null;
	
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

//	public Map<Stmt, Set<Stmt>> getPreferenceValue2ViewMap() {
//		return preferenceValue2ViewMap;
//	}

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
	
	private Set<String> loadAndroidCallBackListeners(){
		Set<String> androidCallbacks = new HashSet<String>();
		BufferedReader rdr = null;
		try {
			String fileName = CALLBACK_LIST_FILE_NAME;
			if (!new File(fileName).exists()) {
				fileName = "../soot-infoflow-android/AndroidCallbacks.txt";
				if (!new File(fileName).exists())
					throw new RuntimeException("Callback definition file not found");
			}
			rdr = new BufferedReader(new FileReader(fileName));
			String line;
			while ((line = rdr.readLine()) != null)
				if (!line.isEmpty())
					androidCallbacks.add(line);
		}
		catch(Exception e){
			System.err.println("failed to read callback file");
			System.exit(1);
		}
		
		return androidCallbacks;
	}
	
	public FlowPathSet(){
		this.lst = new ArrayList<FlowPath>();
		this.callbackListenerSet = loadAndroidCallBackListeners();
		this.dynamicTextMap = new HashMap<Stmt, Set<String>>();
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
		//extractDynamicTexts();
		
		viewFlowMap = new HashMap<Integer, Set<Integer>>();
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

	public void addFlowPath(FlowPath fp){
		if(fp.getId() != -1){
			System.out.println("NULIST: ERROR: failed to addFlowPath: the path has been added already.");
			return ;
		}
		if(addedFlowSet.contains(fp.getSignature())){
			System.out.println("NULIST: ERROR: failed to addFlowPath: the path has been added already2.");
			return ;
		}
		
		if(fp.getSource().getSource().toString().contains(FIND_VIEW_BY_ID_SIGNATURE_STR) ||
				isDynamicWidgetOrDialogSource(fp.getSource().getSource())){
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
			if(!gData.isSensitiveUISource(fp.getSource().getSource())){
				System.out.println("IS SENSITIVE:"+fp.getSource().getSource());
				return;
			}
			else{
				System.out.println("IS NOT SENSITIVE:"+fp.getSource().getSource());
			}
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
		//check if source is a view.
		lst.add(fp);
		addedFlowSet.add(fp.getSignature());
	}
	
	public void updateViewsInPaths(){
		if(sourceSinkMgr == null){
			System.out.println("Error: sourceSinkManager has not been set!");
			return ;
		}
		for(FlowPath fp : lst){
			List<Integer> viewIDs = fp.findViewsInPaths(sourceSinkMgr);
			for(Integer id : viewIDs)
				addViewFlowMapping(fp.getId(), id);	
		}
	}
	
	static private boolean isDynamicWidgetOrDialogSource(Stmt stmt){
		if(stmt instanceof DefinitionStmt){
			DefinitionStmt as = (DefinitionStmt)stmt;
			Value right = as.getRightOp();
			if(right instanceof NewExpr){
				String rightName = ((NewExpr)right).getType().getEscapedName();
				String[] elems = rightName.split("\\.");
				//System.out.println("DDDDD:"+rightName+" "+elems.length);
				if(elems!=null && elems.length>0){
					//View
					if(elems.length>1 && elems[elems.length-2].equals("widget") && elems[0].equals("android"))
						return true;
					else if(elems.length>=3 && 
							elems[0].equals("android") && elems[1].equals("app") && 
							elems[elems.length-1].contains("Dialog")){
						return true;
					}
				}
			}
		}
		return false;
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
		 if(rs.size() > 1){
			 System.out.println("DEBUG34: Stmt "+s+" hit "+rs.size()+" flows.");
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
		
		//Alert Dialog
		this.eventListenerMap.put("onClick", "setPositiveButton");
		this.eventListenerMap.put("onClick", "setNegativeButton");
		this.eventListenerMap.put("onClick", "setButton");
		this.eventListenerMap.put("onClick", "setMultiChoiceItems");
		this.eventListenerMap.put("onClick", "setNeutralButton");
		this.eventListenerMap.put("onCancel", "setOnCancelListener");
		//setOnDismissListener onDismiss
		//setOnItemSelectedListener onItemSelected onNothingSelected
		//setSingleChoiceItems  onClick
		//setOnDateSetListener  onDateSet
		
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
		    	//test
		    	if(s.containsInvokeExpr()){
		    		InvokeExpr expr = s.getInvokeExpr();
		    		SootMethod invokedM = expr.getMethod();
		    		for(int i=0; i<invokedM.getParameterCount(); i++){
		    			Type type = invokedM.getParameterType(i);
		    			if(callbackListenerSet.contains(type.getEscapedName()) ){
		    				System.out.println("TTTTT: "+type.getEscapedName()+" - "+expr.getArg(i).getType());
		    				System.out.println("     : "+s);
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
//		    		if(eventRegistryMethodSet.contains(invokedM.getName())){
//		    			if(invokedM.getParameterCount() == 1){ //e.g., setOnClickListener
//		    				Value arg = expr.getArg(0); 
//		    				String type = arg.getType().toString();
//		    				//System.out.println("NULIST RC:"+type+" //"+invokedM.getName());
//		    				if(registryMap.containsKey(type))
//		    					registryMap.get(type).add(s);
//		    				else{
//		    					List<Stmt> lst = new ArrayList<Stmt>();
//		    					lst.add(s);
//		    					registryMap.put(type, lst);
//		    				}
//		    				System.out.println("DEBUG4:"+type+" -> "+s);
//		    			}
//		    		}
		    			
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
				System.out.println("Display LAYOUT MAP:"+cls+" => "+id);
			}
		}
		for(String listenerClsName : registryMap.keySet()){
			List<Stmt> list = registryMap.get(listenerClsName);
			for(Stmt stmt : list){
				System.out.println("Display Registry Map:"+listenerClsName+" => "+stmt);
			}
		}
		
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
	
	public void displayFlowPaths(){
		System.out.println("Display all the flowpath:");
		for(FlowPath fp : lst){
			System.out.println("Flow:"+fp.getSource()+" => "+fp.getSink());
		}
	}
	/* Exactly the same! 
	 * Not include two different InstanceFieldRefs point to the same value. */
	/*
	private boolean sameValue(Value left, Value right){
		if((left instanceof Local) && (right instanceof Local))
			return ((Local)left).getName().equals(((Local)right).getName());
		else if((left instanceof StaticFieldRef) && (right instanceof StaticFieldRef))
			return ((StaticFieldRef)left).getFieldRef().getSignature().equals(((StaticFieldRef)right).getFieldRef().getSignature());
		else if((left instanceof InstanceFieldRef) && (right instanceof InstanceFieldRef)){
			if( ((InstanceFieldRef)left).getField().getName().equals( ((InstanceFieldRef)right).getField().getName()))
				return sameValue(((InstanceFieldRef)left).getBase(), ((InstanceFieldRef)right).getBase());	
		}
		else if((left instanceof ArrayRef) && (right instanceof ArrayRef)){
			//TODO: what if $r1[$r2], $r1[$r4], but $r2 is the same with $r4
			return sameValue(((ArrayRef)left).getBase(), ((ArrayRef)right).getBase()) &&
					sameValue(((ArrayRef)left).getIndex(), ((ArrayRef)right).getIndex());
		}
		else if((left instanceof Constant) && (right instanceof Constant))
			return left.toString().equals(right.toString());
		return false;
	}
	
	private boolean pointToSameValue(Value candidate, Value target, List<NUAccessPath> bases){
		if(sameValue(candidate, target))
			return true;
		if(! (candidate instanceof InstanceFieldRef) )
			return false;
		if(! (target instanceof InstanceFieldRef) )
			return false;
		
		if(((InstanceFieldRef)candidate).getField().getName().equals(((InstanceFieldRef)target).getField().getName())){
			if(NUAccessPath.containsAccessPath(bases, ((InstanceFieldRef)candidate).getBase()))
				return true;
		}
		return false;
	}
	
	private void findViewDefStmt(Stmt stmt, Value target, List<NUAccessPath> bases,
			BiDiInterproceduralCFG<Unit, SootMethod> cfg, Set<Stmt> visited, Set<Stmt> rs){
		if(visited.contains(stmt))
			return ;
		visited.add(stmt);
		if(cfg == null){
			System.err.println("Error: findViewDefStmt: cfg is not set");
			return ;
		}
		
		if(stmt instanceof AssignStmt){
			AssignStmt as = (AssignStmt)stmt;
			if(sameValue(as.getLeftOp(),target) ){
//				System.out.println("   AssignStmt sameValue: T"+target+" AS:" +as);
//				System.out.println("   NAP: "+NUAccessPath.listAPToString(bases));
				findViewDefStmtHelper(as, target, bases, cfg, visited, rs);
				return ;
			}
			else if(target instanceof InstanceFieldRef){ //as.getLeftOp() != target
				//if left != right, we only care if target is InstanceFieldRef
				//because its possible a different Value points to target (alias)
				
				//check if left op points to the target
				Value left = as.getLeftOp();
				if(pointToSameValue(left, target, bases)){
//					System.out.println("   AssignStmt pointToSameValue: T:"+target+" AS:" +as);
//					System.out.println("   NAP: "+NUAccessPath.listAPToString(bases));
					findViewDefStmtHelper(as, target, bases, cfg, visited, rs);	
					return ;
				}
				
				//left op doesn't point to the target
				//check if left is a prefix of one of bases
				if (!as.containsInvokeExpr() && NUAccessPath.containsAccessPathWithPrefix(bases, left)){
					List<NUAccessPath> lst= NUAccessPath.findAccessPathWithPrefix(bases, left);
					for(NUAccessPath ap : lst){
						ap.replacePrefix(left, as.getRightOp());
//						System.out.println("   AssignStmt prefix: T:"+target+" AccessPath:" +ap+" AS:"+as);
//						System.out.println("   NAP: "+NUAccessPath.listAPToString(bases));
					}
				}
				else if(NUAccessPath.containsAccessPathWithPrefix(bases, left)){
					List<NUAccessPath> lst= NUAccessPath.findAccessPathWithPrefix(bases, left);
					//====process called method============
					//TODO: HAVE NOT TESTED!!!
					InvokeExpr ie = stmt.getInvokeExpr();
					SootMethod sm = ie.getMethod();
					if(sm.hasActiveBody()){
						UnitGraph g = new ExceptionalUnitGraph(sm.getActiveBody());
						List<NUAccessPath> newBases = new ArrayList<NUAccessPath>();
						//if needs to replace base with $r0
						if(ie instanceof InstanceInvokeExpr){ 
							Value base = ((InstanceInvokeExpr) ie).getBase();
							List<NUAccessPath> tmp = NUAccessPath.findAccessPathWithPrefix(bases, base);
							if(tmp!=null && tmp.size()>0){
								Local thisVar = null;
								Iterator<Unit> it = g.iterator();
								try{
									while(it.hasNext()){
										Stmt s = (Stmt)it.next();
										if(s instanceof IdentityStmt && ((IdentityStmt) s).getRightOp() instanceof ThisRef){
											thisVar = (Local)((IdentityStmt) s).getLeftOp();
											break;
										}
									}
								}
								catch(Exception e){}
								
								if(thisVar != null){
									for(NUAccessPath ap : tmp){
										NUAccessPath newAP = new NUAccessPath(ap);
										newAP.replacePrefix(base, thisVar);
										newBases.add(newAP);
									}
								}
							}
						}
						
						for(Unit u : g.getTails()){
							List<NUAccessPath> newBases2 = new ArrayList<NUAccessPath>();
							newBases2.addAll(newBases);
							if(u instanceof ReturnStmt){
								//replace left with return value
								for(NUAccessPath ap : lst){
									NUAccessPath newAP = new NUAccessPath(ap);
									newAP.replacePrefix(left, ((ReturnStmt) u).getOp());
									newBases2.add(newAP);
								}
								//System.out.println("YYYYYY:"+((ReturnStmt) u).getOp()+"  "+u);
								Set<Stmt> newVisited = null;
								if(g.getTails().size() == 1)
									newVisited = visited;
								else{
									newVisited = new HashSet<Stmt>();
									newVisited.addAll(visited);
								}
								findViewDefStmt((Stmt)u, target, newBases2, cfg, newVisited, rs);
							}
							else{
								System.out.println("Error: findViewDefStmtHelper"+u.getClass()+"  "+u);
							}
						}
					}// sm.hasActiveBody
					//=====================================
					
					for(NUAccessPath ap : lst)
						bases.remove(ap);
					if(bases == null)
						return ;
				}
			}
		}
		else if(stmt instanceof IdentityStmt){
			IdentityStmt is = (IdentityStmt)stmt;
			//left value is target or left value is a prefix of target
			if(pointToSameValue( is.getLeftOp(),target, bases) || 
				(target instanceof InstanceFieldRef && NUAccessPath.containsAccessPathWithPrefix(
							bases, ((IdentityStmt) stmt).getLeftOp()))){
//				System.out.println("   IdentityStmt pointToSameValue: "+target+" IS:"+is);
//				System.out.println("   NAP: "+NUAccessPath.listAPToString(bases));
				if(is.getRightOp() instanceof ParameterRef){
					ParameterRef right = (ParameterRef)(is.getRightOp());
					Value left = ((IdentityStmt) stmt).getLeftOp();
					int idx = right.getIndex();
					Collection<Unit> callers = cfg.getCallersOf(cfg.getMethodOf(stmt));
					if(callers != null && callers.size()>0){
						for(Unit caller : callers){
							InvokeExpr ie = ((Stmt)caller).getInvokeExpr();
							if(idx >= ie.getArgCount()) continue;
							Value arg = ie.getArg(idx);
							Set<Stmt> newVisited = null;
							if(callers.size() == 1)
								newVisited = visited;
							else{
								newVisited = new HashSet<Stmt>();
								newVisited.addAll(visited);
							}
							if(pointToSameValue(left, target, bases)){
								List<NUAccessPath> newBases = new ArrayList<NUAccessPath>();
								if(arg instanceof InstanceFieldRef)
									newBases.add(new NUAccessPath(((InstanceFieldRef) arg).getBase()));
//								System.out.println("   Caller 1:"+caller+"@"+cfg.getMethodOf(caller).getSignature());
//								System.out.println("   NAP: "+NUAccessPath.listAPToString(newBases));
								findViewDefStmt((Stmt) caller, arg, newBases, cfg, newVisited, rs);
							}
							else{
								List<NUAccessPath> newBases = new ArrayList<NUAccessPath>();
								List<NUAccessPath> fitBases = NUAccessPath.findAccessPathWithPrefix(bases, left);
								for(NUAccessPath np: fitBases){
									NUAccessPath newNP = new NUAccessPath(np);
									newNP.replacePrefix(left, arg);
									newBases.add(newNP);
								}
								if(arg instanceof InstanceFieldRef)
									NUAccessPath.addUniqueAccessPath(newBases, ((InstanceFieldRef) arg).getBase());
//								System.out.println("   Caller 2:"+caller+"@"+cfg.getMethodOf(caller).getSignature());
//								System.out.println("   NAP: "+NUAccessPath.listAPToString(newBases));
								findViewDefStmt((Stmt) caller, target, newBases, cfg, newVisited, rs);
							}
						}
					}
				}
				else if(is.getRightOp() instanceof ThisRef){
					if(pointToSameValue(is.getLeftOp(),target, bases)){
						System.out.println("ALERT: shouldn't come here findViewDefStmt 1");
						return;
					}
					try{
						List<SootMethod> methods = cfg.getMethodOf(stmt).getDeclaringClass().getMethods();
						for(SootMethod method : methods){
							if(method == cfg.getMethodOf(stmt)) continue;
							if(!method.hasActiveBody()) continue;
							UnitGraph g = new ExceptionalUnitGraph(method.getActiveBody());
//							System.out.println("   Start "+method.getName()+"@"+method.getDeclaringClass().getName()+" T:"+target);
//							System.out.println("   NAP: "+NUAccessPath.listAPToString(bases));
						    for(Unit u : g.getTails()){
						    	List<NUAccessPath> tmpBases = new ArrayList<NUAccessPath>();
								List<NUAccessPath> fitBases = NUAccessPath.findAccessPathWithPrefix(bases, is.getLeftOp());
								for(NUAccessPath np: fitBases)
									tmpBases.add(new NUAccessPath(np));
//								System.out.println("   NAP NewBases: "+NUAccessPath.listAPToString(tmpBases));
								Set<Stmt> newVisited = null;
								if(g.getTails().size() == 1)
									newVisited = visited;
								else{
									newVisited = new HashSet<Stmt>();
									newVisited.addAll(visited);
								}
								findViewDefStmt((Stmt)u, target, tmpBases, cfg, newVisited, rs);
						    }
						}
					}
					catch(Exception e){
						System.out.println("Error in findViewDefStmt: "+e+" "+stmt);
					}
				}
				return ;
			}
//			else if(target instanceof InstanceFieldRef){
//				for(Value b : bases){
//					System.out.println("DD "+target+" VS "+b);
//				}
//			}
		}
		else if(stmt.containsInvokeExpr() && stmt.getInvokeExpr() instanceof InstanceInvokeExpr){
			InstanceInvokeExpr iie = (InstanceInvokeExpr)stmt.getInvokeExpr();
			Value base = iie.getBase();
			if(NUAccessPath.containsAccessPathWithPrefix(bases, base)){
				List<NUAccessPath> lst= NUAccessPath.findAccessPathWithPrefix(bases, base);
				SootMethod method = iie.getMethod();
				if(method.hasActiveBody()){
					UnitGraph g = new ExceptionalUnitGraph(method.getActiveBody());
					Local thisVar = null;
					Iterator<Unit> it = g.iterator();
					try{
						while(it.hasNext()){
							Stmt s = (Stmt)it.next();
							if(s instanceof IdentityStmt && ((IdentityStmt) s).getRightOp() instanceof ThisRef){
								thisVar = (Local)((IdentityStmt) s).getLeftOp();
								break;
							}
						}
					}
					catch(Exception e){}
					if(thisVar != null){
						for(Unit u : g.getTails()){
							List<NUAccessPath> newBases = new ArrayList<NUAccessPath>();
							for(NUAccessPath ap : lst){
								NUAccessPath newap = new NUAccessPath(ap);
								newap.replacePrefix(base, thisVar);
								newBases.add(newap);
							}
							
//							System.out.println("   InvokeExpr prefix: T:"+target+" Base:" +base+" AS:"+stmt+"@"+cfg.getMethodOf(stmt));
//							System.out.println("   NAP New: "+NUAccessPath.listAPToString(bases)+" "+visited.size()+" Tails:"+g.getTails().size());
							Set<Stmt> newVisited = null;
							if(g.getTails().size() == 1)
								newVisited = visited;
							else{
								newVisited = new HashSet<Stmt>();
								newVisited.addAll(visited);
							}
							findViewDefStmt((Stmt)u, target, newBases, cfg, newVisited, rs);
						}
					}
				}
			}
		}
		
		for (Unit pred : cfg.getPredsOf(stmt)) {
			if (!(pred instanceof Stmt))
				continue;
			Set<Stmt> newVisited = null;
			if(cfg.getPredsOf(stmt).size() == 1)
				newVisited = visited;
			else{
				newVisited = new HashSet<Stmt>();
				newVisited.addAll(visited);
			}
			findViewDefStmt((Stmt) pred, target, bases, cfg, newVisited, rs);
		}	
	}
	
	private void findViewDefStmtHelper(AssignStmt stmt,  Value target, List<NUAccessPath> bases,
			BiDiInterproceduralCFG<Unit, SootMethod> cfg, Set<Stmt> visited, Set<Stmt> rs){
		//either isSame(target, stmt.getLeftOp()) or 
		//target.fieldName==stmt.getLeftOp().fieldName && NUAccessPath.containsAccessPath(bases, stmt.getLeftOp().getBase())
		Value right = stmt.getRightOp();
//		System.out.println("      Terminal"+target+" Stmt:"+stmt);
//		System.out.println("      NAP: "+NUAccessPath.listAPToString(bases));
		if(right instanceof InvokeExpr){
			if(stmt.getInvokeExpr().getMethod().getName().equals(FIND_VIEW_BY_ID))
				rs.add(stmt);
			else  {
				InvokeExpr ie = stmt.getInvokeExpr();
				SootMethod sm = ie.getMethod();
				if(sm.hasActiveBody()){
					UnitGraph g = new ExceptionalUnitGraph(sm.getActiveBody());
					List<NUAccessPath> newBases = new ArrayList<NUAccessPath>();
					if(ie instanceof InstanceInvokeExpr){ //if needs to replace base with $r0
						Value base = ((InstanceInvokeExpr) ie).getBase();
						List<NUAccessPath> tmp = NUAccessPath.findAccessPathWithPrefix(bases, base);
						if(tmp!=null && tmp.size()>0){
							Local thisVar = null;
							Iterator<Unit> it = g.iterator();
							try{
								while(it.hasNext()){
									Stmt s = (Stmt)it.next();
									if(s instanceof IdentityStmt && ((IdentityStmt) s).getRightOp() instanceof ThisRef){
										thisVar = (Local)((IdentityStmt) s).getLeftOp();
										break;
									}
								}
							}
							catch(Exception e){}
							
							if(thisVar != null){
								for(NUAccessPath ap : tmp){
									NUAccessPath newAP = new NUAccessPath(ap);
									newAP.replacePrefix(base, thisVar);
									newBases.add(newAP);
								}
							}
						}
					}
					
					for(Unit u : g.getTails()){
						List<NUAccessPath> newBases2 = new ArrayList<NUAccessPath>();
						newBases2.addAll(newBases);
						if(u instanceof ReturnStmt){
							//System.out.println("YYYYYY:"+((ReturnStmt) u).getOp()+"  "+u);
							Set<Stmt> newVisited = null;
							if(g.getTails().size() == 1)
								newVisited = visited;
							else{
								newVisited = new HashSet<Stmt>();
								newVisited.addAll(visited);
							}
							findViewDefStmt((Stmt)u, ((ReturnStmt) u).getOp(), newBases2, cfg, newVisited, rs);
						}
						else{
							System.out.println("Error: findViewDefStmtHelper"+u.getClass()+"  "+u);
						}
					}
				}// sm.hasActiveBody
			}
		}
		else if(right instanceof NewExpr){
			String rightName = ((NewExpr)right).getType().getEscapedName();
			String[] elems = rightName.split("\\.");
			if(elems!=null && elems.length>0){
				if(elems.length>1 && elems[elems.length-2].equals("widget") && elems[0].equals("android")){
					rs.add(stmt);  //view
				}
				else if(elems.length>=3 && 
						elems[0].equals("android") && elems[1].equals("app") && 
						elems[elems.length-1].contains("Dialog")){ //dialog
					rs.add(stmt);
				}
			}
			else  System.out.println("ATTENTION: unknown def new expr:"+stmt);
		}
		else if(right instanceof CastExpr ){
			for (Unit pred : cfg.getPredsOf(stmt)) {
				if (!(pred instanceof Stmt))
					continue;
				Value newTarget = ((CastExpr) right).getOp();
				List<NUAccessPath> newBases = new ArrayList<NUAccessPath>();
				for(NUAccessPath np: bases)
					newBases.add(new NUAccessPath(np) );
				if(newTarget instanceof InstanceFieldRef) 
					NUAccessPath.addUniqueAccessPath(newBases, ((InstanceFieldRef) newTarget).getBase());
				Set<Stmt> newVisited = null;
				if(cfg.getPredsOf(stmt).size() == 1)
					newVisited = visited;
				else{
					newVisited = new HashSet<Stmt>();
					newVisited.addAll(visited);
				}
				findViewDefStmt((Stmt) pred, newTarget, newBases, cfg, newVisited, rs);
			}
		}
		else if(right instanceof Local || right instanceof StaticFieldRef){
			for (Unit pred : cfg.getPredsOf(stmt)) {
				if (!(pred instanceof Stmt))
					continue;
				List<NUAccessPath> newBases = new ArrayList<NUAccessPath>();
				for(NUAccessPath np: bases)
					newBases.add(new NUAccessPath(np) );
				//NUAccessPath current = NUAccessPath.findAccessPath(newBases, stmt.getLeftOp());
				Set<Stmt> newVisited = null;
				if(cfg.getPredsOf(stmt).size() == 1)
					newVisited = visited;
				else{
					newVisited = new HashSet<Stmt>();
					newVisited.addAll(visited);
				}
				findViewDefStmt((Stmt) pred, right, newBases, cfg, newVisited, rs);
			}
		}
		else if(right instanceof InstanceFieldRef){
			for (Unit pred : cfg.getPredsOf(stmt)) {
				if (!(pred instanceof Stmt))
					continue;
				List<NUAccessPath> newBases = new ArrayList<NUAccessPath>();
				for(NUAccessPath np: bases)
					newBases.add(new NUAccessPath(np) );
				NUAccessPath.addUniqueAccessPath(newBases, ((InstanceFieldRef) right).getBase());
				Set<Stmt> newVisited = null;
				if(cfg.getPredsOf(stmt).size() == 1)
					newVisited = visited;
				else{
					newVisited = new HashSet<Stmt>();
					newVisited.addAll(visited);
				}
				findViewDefStmt((Stmt) pred, right, newBases, cfg, newVisited, rs);
			}
		}
		else 
			System.out.println("ATTENTION: unknown def expr:"+stmt);
		return;
	}
	*/
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
