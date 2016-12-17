package soot.jimple.infoflow.nu;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Queue;
import java.util.Set;

import soot.Scene;
import soot.SootMethod;
import soot.Unit;
import soot.ValueBox;
import soot.jimple.BreakpointStmt;
import soot.jimple.IdentityStmt;
import soot.jimple.InvokeExpr;
import soot.jimple.MonitorStmt;
import soot.jimple.RetStmt;
import soot.jimple.ReturnStmt;
import soot.jimple.ReturnVoidStmt;
import soot.jimple.Stmt;
import soot.jimple.infoflow.results.ResultSinkInfo;
import soot.jimple.infoflow.results.ResultSourceInfo;
import soot.jimple.infoflow.solver.cfg.IInfoflowCFG;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.Edge;
import soot.toolkits.graph.ExceptionalUnitGraph;
import soot.toolkits.graph.UnitGraph;

public class FlowPath {
	/* 
	 * Set by FlowPathSet, the number is unique in a FlowPathSet
	 * -1 means the value has not been set yet.
	 * */
	int id;
	
	ResultSinkInfo sink;
	ResultSourceInfo source;
	IInfoflowCFG icfg;
	CallGraph cg;
	List<List<Stmt>> pathRS;
	//stmt@method -> Stmt
	Map<String, Stmt> pathStmtMap;
	boolean debug = false;

	private Map<String, String> eventListenerMap = null;
	private Set<String> lifeCycleEventListenerSet = null;
	private Map<String, List<Stmt>> registryMap = null;
	
	public FlowPath(IInfoflowCFG icfg, ResultSourceInfo source, ResultSinkInfo sink,
			Map<String, String> eventListenerMap, Set<String> lifeCycleEventListenerSet,
			Map<String, List<Stmt>> registryMap){
		this.icfg = icfg;
		this.pathStmtMap = new HashMap<String, Stmt>();
		this.source = source;
		this.sink = sink;
		this.cg =  Scene.v().getCallGraph();
		this.registryMap = registryMap;
		this.eventListenerMap = eventListenerMap;
		this.lifeCycleEventListenerSet = lifeCycleEventListenerSet;
		this.id = -1;
		//buildEventListenerMap();
		
		pathRS = new ArrayList<List<Stmt>>();
		buildFlowFullPath(source.getPath());
		List<Stmt> triggers = findFlowTrigger();
		//TODO: the order of pathRS is no use, so we might change it's type to
		// List<Stmt>, including the affected stmts.
		if(triggers.size() > 0){
			for(Stmt stmt : triggers){
				pathStmtMap.put(buildStmtSignature(stmt, icfg), stmt);
			}
			pathRS.add(triggers);
		}
		
	}
	
	//TODO: no use
	private void buildEventListenerMap(){
		this.eventListenerMap = new HashMap<String, String>();
		this.eventListenerMap.put("onClick", "setOnClickListener");
		this.eventListenerMap.put("onLongClick", "setOnLongClickListener");
		
		this.eventListenerMap.put("onFocusChange", "setOnFocusChangeListener");
		this.eventListenerMap.put("onFocusChanged", "setOnFocusChangeListener");
		
		this.eventListenerMap.put("onKey", "setOnKeyListener");
		this.eventListenerMap.put("onKeyDown", "setOnKeyListener");
		this.eventListenerMap.put("onKeyUp", "setOnKeyListener");
		
		this.eventListenerMap.put("onTouchEvent", "setOnTouchListener");
		this.eventListenerMap.put("onTouch", "setOnTouchListener");
		
		this.lifeCycleEventListenerSet = new HashSet<String>();
		this.lifeCycleEventListenerSet.add("onCreate");
		this.lifeCycleEventListenerSet.add("onPause");
		this.lifeCycleEventListenerSet.add("onStart");
		this.lifeCycleEventListenerSet.add("onResume");
		this.lifeCycleEventListenerSet.add("onRestart");
		this.lifeCycleEventListenerSet.add("onStop");
		this.lifeCycleEventListenerSet.add("onDestroy");
		
	}
	
	private List<Stmt> findFlowTrigger(){
		
		System.out.println("NULIST: Start finding trigger for flow: "+this.source.getSource());
		//Stmt src = this.source.getSource();
		if(this.icfg==null){
			System.out.println("NULIST DEBUG: no parent method for source");
			return null;
		}
		
		Queue<SootMethod> queue = new LinkedList<SootMethod>();
		Set<String> visited = new HashSet<String>();
		
		for(Stmt stmt : source.getPath()){
			SootMethod sm = icfg.getMethodOf(stmt);
			if(visited.contains(sm.getSignature()))
				continue;
			queue.add(sm);
			visited.add(sm.getSignature());
		}
		List<Stmt> rs = new ArrayList<Stmt>();
		List<Stmt> rsLifeCycle = new ArrayList<Stmt>();
		while(!queue.isEmpty()){
			SootMethod sm = queue.poll();
			if(this.eventListenerMap.containsKey(sm.getName()) ){
//				System.out.println("NULIST DEBUG: Found trigger1: "+sm.getDeclaringClass().toString());
				List<Stmt> lst = this.registryMap.get(sm.getDeclaringClass().toString());
				if(lst == null) continue;
				for(Stmt s : lst){
//					System.out.println("NULIST DEBUG:  registrymethod: "+s);
					rs.add(s);
				}
			}
			else if(this.lifeCycleEventListenerSet.contains(sm.getName())){
//				System.out.println("NULIST DEBUG: Found trigger2: "+sm.getSignature());
				List<Stmt> lst = this.registryMap.get(sm.getSignature());
				if(lst == null) continue;
				for(Stmt s : lst){
//					System.out.println("NULIST DEBUG:  registrymethod: "+s);
					rsLifeCycle.add(s);
				}
			}
			else{
				Iterator<Edge> edges = cg.edgesInto(sm);
				while(edges.hasNext()){
					Edge edge = edges.next();
					SootMethod predecessor = edge.getSrc().method();
					if(predecessor == null) continue;
					if(!visited.contains(predecessor.getSignature())){
						queue.add(predecessor);
					}
				}
			}
		}
		System.out.println("NULIST: Done finding trigger for flow: "+this.source.getSource());
		if(rs.size() > 0){
			for(Stmt stmt: rs)
				System.out.println("NULIST:  event stmt: "+stmt);
			return rs;
		}
		else if(rsLifeCycle.size() > 0){
			for(Stmt stmt : rsLifeCycle)
				System.out.println("NULIST:  lifecycle stmt: "+stmt);
			return rsLifeCycle;
		}
		else{
			System.out.println("NULIST:  no trigger found!");
		}
		
		return rs;
	}
	
	public Stmt findStmtFromFlowPath(Stmt s, IInfoflowCFG newIcfg){
		return pathStmtMap.get(buildStmtSignature(s, newIcfg));
	}
	
	private String buildStmtSignature(Stmt s, IInfoflowCFG newIcfg){
		if(newIcfg == null)
			return s.toString()+"@null";
		
		SootMethod curMethod = newIcfg.getMethodOf(s);
		if(curMethod == null)
			return s.toString()+"@null";
		else
			return s.toString()+"@"+curMethod.getSignature();
	}
	
	private void buildFlowFullPath(Stmt[] path){
		List<List<Stmt>> rs = pathRS;
		
		if(path.length>0 && path[0].toString().contains("double getLongitude()"))
			debug = true;
		for(int i=0; i<path.length-1; i++){
			Stmt cur = path[i];
			Stmt next = path[i+1];
			SootMethod curMethod = icfg.getMethodOf(cur);
			SootMethod nextMethod = icfg.getMethodOf(next);
			
//			if(debug){
//				System.out.println("DEBUG6: C "+curMethod.getSignature()+" =>"+cur);
//				System.out.println("DEBUG6: N "+nextMethod.getSignature()+" =>"+next);
//				//System.out.println("DEBUG6: --"+curMethod.getSignature().equals(anObject));
//			}
			if(curMethod.getSignature().equals(nextMethod.getSignature())){
				List<List<Stmt>> subrs = addStmtIntraProcedure(curMethod, cur, next);
				addMultipleGroupStmtsToList(rs, subrs);
			}
			else {
				if(cur.containsInvokeExpr()){
					InvokeExpr ie = cur.getInvokeExpr();
					if(ie.getMethod().getSignature().equals(nextMethod.getSignature())){
						//System.out.println("DEBUG: "+ie+" VS "+nextMethod);
						addOneStmtToList(rs, cur); //add current function call
						List<List<Stmt>> subrs = addStmtIntraProcedure(nextMethod, null, next);
						addMultipleGroupStmtsToList(rs, subrs); //add stmts from the begining.
					}
					else 
						addOneStmtToList(rs, cur);
				}
				else {
					addOneStmtToList(rs, cur);
				}
			}
		}
		addOneStmtToList(rs, path[path.length-1]);
		
		int cnt = 0;
		for(List<Stmt> lst : rs){
			System.out.println("Building Full Path: "+cnt+++" Size:"+lst.size());
			for(Stmt s : lst){
				pathStmtMap.put(buildStmtSignature(s, icfg), s);
//				List<ValueBox> boxes = s.getUseBoxes();
				System.out.println("  "+icfg.getMethodOf(s).getName()+":"+s);
			}
		}
	}
	
	private void addMultipleGroupStmtsToList(List<List<Stmt>> lst, List<List<Stmt>> adds){
		if(lst.size() == 0){
			for(List<Stmt> la : adds)
				lst.add(la);
		}
		else{
			for(List<Stmt> l : lst){
				for(List<Stmt> la : adds){
					for(Stmt s : la)
						addStmtToList(l, s);
				}
			}
		}
	}
	private void addOneStmtToList(List<List<Stmt>> lst, Stmt stmt){
		if(lst.size() == 0){
			List<Stmt> tmp = new ArrayList<Stmt>();
			tmp.add(stmt);
			lst.add(tmp);
		}
		else{
			for(List<Stmt> l : lst){
				for(Stmt s : l)
					if(s.equals(stmt))
						return;
				addStmtToList(l, stmt);
			}
		}
	}
	private boolean isSameStmt(Stmt s1, Stmt s2){
		if(s1.toString().equals(s2.toString())){
			SootMethod m1 = icfg.getMethodOf(s1);
			SootMethod m2 = icfg.getMethodOf(s2);
			if(m1==null && m2==null)
				return true;
			else if(m1==null || m2==null)
				return false;
			else if(m1.getSignature().equals(m2.getSignature()))
				return true;
		}
		return false;
	}
	
	private void addStmtToList(List<Stmt> lst, Stmt stmt){
		if(stmt instanceof IdentityStmt || stmt instanceof BreakpointStmt ||
				stmt instanceof MonitorStmt || stmt instanceof RetStmt || 
				stmt instanceof ReturnStmt || stmt instanceof ReturnVoidStmt)
			return ;	
		for(Stmt s : lst)
			if(isSameStmt(s, stmt)){
				System.out.println("found the same stmt");
				return ;
			}
			
//			if(s.equals(stmt))
//				return ;
//			else if (s.toString().equals(stmt.toString())){
//				System.out.println("Two Stmt equal based on string:");
//				System.out.println("  :"+s+" VS "+stmt);
//				
//				boolean rs = icfg.getMethodOf(s).toString().equals(icfg.getMethodOf(stmt).toString());
//				System.out.println("  method::"+rs+" "+icfg.getMethodOf(s)+" // "+icfg.getMethodOf(stmt));
//				
//			}
		lst.add(stmt);
	}
	
	private List<List<Stmt>> addStmtIntraProcedure(SootMethod method, Stmt cur, Stmt end){
		List<List<Stmt>> rs = new ArrayList<List<Stmt>>();
		List<Stmt> curRS = new ArrayList<Stmt>();
		//rs.add(curRS);
		
		if(!method.hasActiveBody() && cur!=null){
			curRS.add(cur);
			return rs;
		}
		else if(!method.hasActiveBody()){
			return rs;
		}
		UnitGraph g = new ExceptionalUnitGraph(method.getActiveBody());
		if(cur == null){
			for(Unit u : g.getHeads())
				addStmtIntraProcedureHelper(g, (Stmt)u, end, curRS, rs, new HashSet<Stmt>());
			return rs;
		}
		
		addStmtIntraProcedureHelper(g, cur, end, curRS, rs, new HashSet<Stmt>());
		return rs;
	}
	
	private void addStmtIntraProcedureHelper(UnitGraph g, Stmt cur, Stmt end, List<Stmt> curRS, List<List<Stmt>> rs, Set<Stmt> visited){
		//curRS remain the same when returned.
		if(cur.equals(end)){
			List<Stmt> newRS = new ArrayList<Stmt>();
			for(Stmt s : curRS)
				newRS.add(s);
			rs.add(newRS);
			return ;
		}
		
//		if(debug){
//			//System.out.println("DEBUG6: 1 "+method);
//			System.out.println("DEBUG6: 2 "+cur );
//			System.out.println("DEBUG6: 3 "+end +"\n");
//		}
		
		curRS.add(cur);
		visited.add(cur);
		for(Unit u : g.getSuccsOf(cur)){
			Stmt s = (Stmt)u;
			if(visited.contains(s)) continue;
			addStmtIntraProcedureHelper(g, (Stmt)u, end, curRS, rs, visited);
		}
		visited.remove(cur);
		curRS.remove(curRS.size()-1);
	}
	
	public ResultSinkInfo getSink() {
		return sink;
	}

	public ResultSourceInfo getSource() {
		return source;
	}
	
	public int getId() {
		return id;
	}

	public void setId(int id) {
		this.id = id;
	}
	
	public String getTag(){
		//TODO: could trigger exception because getInvokeExpr returns null.
		try{
			return source.getSource().getInvokeExpr().getMethod().getName()+" => "+sink.getSink().getInvokeExpr().getMethod().getName();
		}
		catch(Exception e){
			return source.getSource()+" => "+sink.getSink();
		}
	}
}
