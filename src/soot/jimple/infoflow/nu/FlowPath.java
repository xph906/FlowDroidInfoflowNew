package soot.jimple.infoflow.nu;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Queue;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import heros.InterproceduralCFG;
import soot.Scene;
import soot.SootMethod;
import soot.Unit;
import soot.ValueBox;
import soot.jimple.BreakpointStmt;
import soot.jimple.IdentityStmt;
import soot.jimple.IfStmt;
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
	//List<List<Stmt>> pathRS;
	List<Stmt> fullPath;
	Stmt[] path;
	//stmt@method -> Stmt
	private Map<String, Stmt> pathStmtMap;
	boolean debug = false;

	private Map<String, String> eventListenerMap = null;
	private Set<String> lifeCycleEventListenerSet = null;
	private Map<String, List<Stmt>> registryMap = null;
	private Set<String> declaringClassSet = null;
	private Set<String> allTrigerMethodSet = null;
	private Pattern callbackMethodNamePatttern = Pattern.compile("^on[A-Z][a-z]");
	
	public FlowPath(IInfoflowCFG icfg, ResultSourceInfo source, ResultSinkInfo sink,
			Map<String, String> eventListenerMap, Set<String> lifeCycleEventListenerSet,
			Map<String, List<Stmt>> registryMap){
		System.out.println("Start FlowPath: "+source.getSource()+"=>"+sink.getSink());
		this.icfg = icfg;
		this.pathStmtMap = new HashMap<String, Stmt>();
		this.source = source;
		this.sink = sink;
		this.cg =  Scene.v().getCallGraph();
		this.registryMap = registryMap;
		this.eventListenerMap = eventListenerMap;
		this.lifeCycleEventListenerSet = lifeCycleEventListenerSet;
		this.id = -1;
		this.declaringClassSet = new HashSet<String>();
		this.allTrigerMethodSet = new HashSet<String>();
		fullPath = new ArrayList<Stmt>();
		this.path = this.source.getPath();
		
		fullPath.add(source.getSource());
		//triggers
		List<Stmt> triggers = findFlowTrigger();
		System.out.println("  Displaying triggers:"+triggers.size());
		for(Stmt stmt : triggers){
			fullPath.add(stmt);
			System.out.println("    "+stmt);
		}
		//predicates
		List<Stmt> predicates = buildFlowFullPath(source.getPath());
		System.out.println("  Displaying predicates:"+triggers.size());
		for(Stmt stmt : predicates){
			fullPath.add(stmt);
			System.out.println("    "+stmt+" @"+icfg.getMethodOf(stmt).getName());
		}
		fullPath.add(sink.getSink());
		
		for(Stmt s : fullPath){
			pathStmtMap.put(buildStmtSignature(s, icfg), s);
			//System.out.println("    "+icfg.getMethodOf(s).getName()+":"+s);
		}
		System.out.println("Done FlowPath: "+source.getSource()+"=>"+sink.getSink()+"\n");
		
//		if(declaringClassSet.size() == 0 && source.getPath()!=null && source.getPath().length>0){
//			System.err.println("Alert an declaring Class because of no class.");
//			declaringClassSet.add(icfg.getMethodOf(source.getPath()[0]).getDeclaringClass().getName() );
//		}
	}
	public FlowPath(FlowPath sourceFP, FlowPath sinkFP){
		this.icfg = sourceFP.icfg;
		this.pathStmtMap = new HashMap<String, Stmt>();
		this.source = sourceFP.getSource();
		this.sink = sinkFP.getSink();
		this.cg =  sourceFP.cg;
		this.registryMap = sourceFP.registryMap;
		this.eventListenerMap = sourceFP.eventListenerMap;
		this.lifeCycleEventListenerSet = sourceFP.lifeCycleEventListenerSet;
		this.id = -1;
		this.declaringClassSet = new HashSet<String>();
		this.allTrigerMethodSet = new HashSet<String>();
		fullPath = new ArrayList<Stmt>();
		this.path = new Stmt[sourceFP.path.length+sinkFP.source.getPath().length];
		int i =0;
		for(Stmt stmt : sourceFP.path)
			this.path[i++] = stmt;
		for(Stmt stmt : sinkFP.path)
			this.path[i++] = stmt;
		
		System.out.println("Start FlowPath2: "+sourceFP.source.getSource()+"=>"+sinkFP.sink.getSink());
		fullPath.add(sourceFP.source.getSource());
		List<Stmt> triggers = findFlowTrigger();
		if(triggers.size() > 0){
			System.out.println("  Displaying triggers:"+triggers.size());
			for(Stmt stmt : triggers){
				fullPath.add(stmt);
				System.out.println("    "+stmt);
			}
		}
		//predicates
		List<Stmt> predicates = buildFlowFullPath(this.path);
		System.out.println("  Displaying predicates:"+triggers.size());
		for(Stmt stmt : predicates){
			fullPath.add(stmt);
			System.out.println("    "+stmt+" @"+icfg.getMethodOf(stmt).getName());
		}
		fullPath.add(sinkFP.sink.getSink());
		for(Stmt s : fullPath){
			pathStmtMap.put(buildStmtSignature(s, icfg), s);
			//System.out.println("    "+icfg.getMethodOf(s).getName()+":"+s);
		}
		System.out.println("Done FlowPath2: "+source.getSource()+"=>"+sink.getSink()+"\n");
	}
	
	private List<Stmt> findFlowTrigger(){
		
		System.out.println("NULIST: Start finding trigger for flow: "+this.source.getSource()+"=>"+sink.getSink());
		System.out.flush();
		//Stmt src = this.source.getSource();
		if(this.icfg==null){
			System.out.println("NULIST DEBUG: no parent method for source");
			return null;
		}
		
		Queue<SootMethod> queue = new LinkedList<SootMethod>();
		Set<String> visited = new HashSet<String>();
		
		//for(Stmt stmt : this.path){
		Stmt srcStmt = source.getSource();
		SootMethod m = icfg.getMethodOf(srcStmt);
		//if(visited.contains(sm.getSignature()))
		//	continue;
		queue.add(m);
		visited.add(m.getSignature());
		//}
		List<Stmt> rs = new ArrayList<Stmt>();
		List<Stmt> rsLifeCycle = new ArrayList<Stmt>();
		while(!queue.isEmpty()){
			SootMethod sm = queue.poll();
			//a regular method could be declared as event handler
			allTrigerMethodSet.add(sm.getName());
			Matcher mat = callbackMethodNamePatttern.matcher(sm.getName());
			if(!this.lifeCycleEventListenerSet.contains(sm.getName()) && mat.find()){
				//System.out.println("NULIST DEBUG: Found trigger1: "+sm.getDeclaringClass().getShortName());
				List<Stmt> lst = this.registryMap.get(sm.getDeclaringClass().toString());
				if(lst != null){
					for(Stmt s : lst){
						System.out.println("NULIST DEBUG888: "+sm.getName()+" => "+s);
						rs.add(s);
					}
				}
			}
			else if(this.lifeCycleEventListenerSet.contains(sm.getName())){
				//System.out.println("NULIST DEBUG: Found trigger2: "+sm.getSignature());
				List<Stmt> lst = this.registryMap.get(sm.getSignature());
				if(lst == null) continue;
				for(Stmt s : lst)
					rsLifeCycle.add(s);
				declaringClassSet.add(sm.getDeclaringClass().getName());
			}
			else{
				Iterator<Edge> edges = cg.edgesInto(sm);
				while(edges.hasNext()){
					Edge edge = edges.next();
					SootMethod predecessor = edge.getSrc().method();
					if(predecessor == null) continue;
					if(!visited.contains(predecessor.getSignature())){
						visited.add(predecessor.getSignature());
						queue.add(predecessor);
					}
				}
			}
		}
		System.out.println("NULIST: Done finding trigger for flow: "+this.source.getSource());
		System.out.flush();
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
		
		//System.out.println("Done findFlowTrigger");
		return rs;
	}
	
	public Set<String> getAllTrigerMethodSet() {
		return allTrigerMethodSet;
	}

	public Set<String> getDeclaringClassSet() {
		return declaringClassSet;
	}

	public Stmt findStmtFromFlowPath(Stmt s, InterproceduralCFG<Unit, SootMethod> newIcfg){
		return pathStmtMap.get(buildStmtSignature(s, newIcfg));
	}
	
	private String buildStmtSignature(Stmt s, InterproceduralCFG<Unit, SootMethod> newIcfg){
		if(newIcfg == null)
			return s.toString()+"@null";
		
		SootMethod curMethod = newIcfg.getMethodOf(s);
		if(curMethod == null)
			return s.toString()+"@null";
		else
			return s.toString()+"@"+curMethod.getSignature();
	}
	
	private List<Stmt> buildFlowFullPath(Stmt[] path){
		List<Stmt> rs = new ArrayList<Stmt>();
		if(path == null || path.length==0)
			return rs;
	
		for(int i=path.length-1; i>0; i--){
//			System.out.println("    buildFlowFullPath "+i+"/"+path.length);
//			System.out.flush();
			Stmt cur = path[i];
			addStmtToList(rs, cur);
			Stmt prev = path[i-1];
			SootMethod curMethod = icfg.getMethodOf(cur);
			SootMethod prevMethod = icfg.getMethodOf(prev);
			
			if(curMethod.getSignature().equals(prevMethod.getSignature())){
				//the two stmts are in the same procedure,
				//so we need to extract all predicate stmts between these two
				//this is an intra-procedure analysis
				Set<Stmt> subrs = addStmtIntraProcedure(curMethod, cur, prev);
				for(Stmt stmt : subrs)
					addStmtToList(rs, stmt);
			}
			else {
				if(prev.containsInvokeExpr()){
					InvokeExpr ie = prev.getInvokeExpr();
					if(ie.getMethod().getSignature().equals(curMethod.getSignature())){
//						System.out.println("    EQUAL:"+curMethod.getSignature());
						//System.out.println("         :"+ie.getMethod().getSignature());
						
						//if current stmt is a call stmt and the next stmt is the stmt in called method
						//addStmtToList(rs, cur); //add current function call
						Set<Stmt> subrs = addStmtIntraProcedure(curMethod, cur, null);
						for(Stmt stmt : subrs){
							addStmtToList(rs, stmt);
//							System.out.println("     STMT:"+stmt);
						}
					}
					else {
//						System.out.println("NOT EQUAL:");
//						System.out.println("         :"+curMethod.getSignature());
//						System.out.println("         :"+ie.getMethod().getSignature());
						addStmtToList(rs, cur);
					}
				}
				else {
					addStmtToList(rs, cur);
				}
			}
		}
		
		addStmtToList(rs, path[0]);
		Collections.reverse(rs);
		return rs;
	}
	

	private boolean isSameStmt(Stmt s1, Stmt s2){
		boolean rs = false;
		if(s1.equals(s2))
			rs = true;
		
		if(s1.toString().equals(s2.toString())){
			SootMethod m1 = icfg.getMethodOf(s1);
			SootMethod m2 = icfg.getMethodOf(s2);
			if(m1==null && m2==null){
				if(rs == false){
					System.err.println("ALERT isSameStmt 1:"+s1+" vs "+s2);
				}
				return true;
			}
			else if(m1==null || m2==null){
				if(rs == true){
					System.err.println("ALERT isSameStmt 2:"+s1+" vs "+s2);
				}
				return false;
			}
			else if(m1.getSignature().equals(m2.getSignature())){
				if(rs == false){
					//TODO: modify this case.
					//System.err.println("ALERT isSameStmt 3:"+s1+" vs "+s2);
					
				}
				return true;
			}
			else{
				if(rs == true){
					System.err.println("ALERT isSameStmt 4:"+s1+" vs "+s2);
				}
			}
		}
		return rs;
	}
	
	private void addStmtToList(List<Stmt> lst, Stmt stmt){
		if( stmt instanceof BreakpointStmt ||
				stmt instanceof MonitorStmt || stmt instanceof RetStmt || 
				stmt instanceof ReturnStmt || stmt instanceof ReturnVoidStmt)
			return ;	
		
		if(!stmt.branches()) return ;
		
		for(Stmt s : lst)
			if(s == stmt)
				return ;
		
		lst.add(stmt);
	}
	
	private Set<Stmt> addStmtIntraProcedure(SootMethod method, Stmt cur, Stmt end){
		Set<Stmt> rs = new HashSet<Stmt>();
		//rs.add(curRS);
		
		if(!method.hasActiveBody() && cur!=null){
			rs.add(cur);
			return rs;
		}
		else if(!method.hasActiveBody()){
			return rs;
		}
		UnitGraph g = new ExceptionalUnitGraph(method.getActiveBody());
		//if cur is null, starts from the heads
		if(end == null){
			for(Unit u : g.getHeads())
				addStmtIntraProcedureHelper(g, cur, (Stmt)u, rs);
			return rs;
		}
		else{
			addStmtIntraProcedureHelper(g, cur, end, rs);
			return rs;
		}
	}
	
	//-1: not hit
	// 1: hit
	// 0: might hit and might not hit.
	private int hitStmt(Stmt beg, Stmt target, UnitGraph g, Set<Stmt> visited){
		Queue<Stmt> queue = new LinkedList<Stmt>();
		visited.add(beg);
		queue.add(beg);
		boolean hit = false;
		boolean miss = false;
		while(!queue.isEmpty()){
			Stmt cur = queue.poll();
			if(cur == target)
				hit = true;
			else{
				for(Unit u : g.getSuccsOf(cur)){
					if(visited.contains((Stmt)u))
						continue;
					visited.add((Stmt)u);
					int sub = hitStmt((Stmt)u, target, g, visited);
					if (sub == 0) return 0;
					else if(sub == 1)
						hit = true;
					else
						miss = true;
				}
			}
		}
		if(hit && miss)
			return 0;
		else if(!hit && !miss)
			return -1;
		else if(hit)
			return 1;
		else
			return -1;
	}
	
	private void addStmtIntraProcedureHelper(UnitGraph g, Stmt cur, Stmt end, Set<Stmt> rs){
		//System.out.println("addStmtIntraProcedureHelper:"+" "+cur+" =>"+end+" "+g.hashCode());
		if(cur.equals(end)){
			rs.add(cur);
			return;
		}
		//System.out.println("                  :"+cur+" N "+end);
		Set<Stmt> visited = new HashSet<Stmt>();
		visited.add(cur);
		Queue<Stmt> queue = new LinkedList<Stmt>();
		queue.add(cur);
		
		while(!queue.isEmpty()){
			cur = queue.poll();
			if(cur == end)
				continue;
			if(cur.branches())
				rs.add(cur);
			
			for(Unit u : g.getPredsOf(cur)){
				Stmt s = (Stmt)u;
				if(visited.contains(s)) continue;
				visited.add(s);
				queue.add(s);
			}
		}
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
	
	//this method is used to differentiate each flow.
	public String getSignature(){
		try{
			return buildStmtSignature(source.getSource(), icfg) + "=>" +
					buildStmtSignature(sink.getSink(), icfg);
		}
		catch(Exception e){
			return source.getSource() +"=>" +sink.getSink();
		}
	}
	//this method is used to 
	public String getTag(){
		//TODO: could trigger exception because getInvokeExpr returns null.
		try{
			SootMethod sourceMethod =  source.getSource().getInvokeExpr().getMethod();
			SootMethod sinkMethod = sink.getSink().getInvokeExpr().getMethod();
			return sourceMethod.getName()+"@"+sourceMethod.getDeclaringClass().getName()+" => "+
					sinkMethod.getName()+"@"+sinkMethod.getDeclaringClass().getName();
		}
		catch(Exception e){
			return source.getSource()+" => "+sink.getSink();
		}
	}
	
	public String toString(){
		StringBuilder sb = new StringBuilder();
		sb.append("PathBegin:\n");
		for(Stmt stmt : fullPath)
			sb.append("  "+stmt.toString()+"@"+icfg.getMethodOf(stmt)+"\n");
		sb.append("PathEnd:\n");
		return sb.toString();
	}
	public String toSourceSinkString(){
		StringBuilder sb = new StringBuilder();
		sb.append(source.getSource().toString());
		sb.append("=>");
		sb.append(sink.getSink().toString());
		return sb.toString();
	}
	
	public boolean equal(FlowPath fp2){
		if(toSourceSinkString().equals(fp2.toSourceSinkString()))
			return true;
		return false;
	}
	
	public int hashCode(){
		return toSourceSinkString().hashCode();
	}
}
