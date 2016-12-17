package soot.jimple.infoflow.nu;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import soot.MethodOrMethodContext;
import soot.Scene;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.jimple.Constant;
import soot.jimple.InvokeExpr;
import soot.jimple.Stmt;
import soot.jimple.infoflow.results.ResultSinkInfo;
import soot.jimple.infoflow.results.ResultSourceInfo;
import soot.jimple.infoflow.solver.cfg.IInfoflowCFG;
import soot.toolkits.graph.ExceptionalUnitGraph;
import soot.toolkits.graph.Orderer;
import soot.toolkits.graph.PseudoTopologicalOrderer;
import soot.toolkits.graph.UnitGraph;
import soot.util.queue.QueueReader;

public class FlowPathSet {
	final String SET_CONTENT_VIEW = "setContentView";
	
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
		 *   1. For eventRegistry (e.g., setOnClickListener), the key is the 
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
	}

	public void addFlowPath(FlowPath fp){
		if(fp.getId() != -1){
			System.out.println("NULIST: ERROR: failed to addFlowPath: the path has been added already.");
			return ;
		}

		fp.setId(lst.size());
		lst.add(fp);
	}
	
	/* return the flow's source's layout*/
//	public Set<Integer> getFlowLayout(){
//		
//	}
	
	public List<Integer> findFlowPath(Stmt s, IInfoflowCFG icfg){
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
		    					System.out.println("NULIST: alert: setContentView's arg is not constant:"+s);
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
				System.out.println("LAYOUT:"+cls+" => "+id);
			}
		}
	}
	
	public Map<String, Set<Integer>> getActivityLayoutMap() {
		return activityLayoutMap;
	}

	public Map<Integer, Set<Integer>> getViewFlowMap() {
		return viewFlowMap;
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
}
