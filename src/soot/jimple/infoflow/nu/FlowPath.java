package soot.jimple.infoflow.nu;

import java.util.ArrayList;
import java.util.Collection;
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

import nu.NUDisplay;
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
import soot.jimple.infoflow.source.ISourceSinkManager;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.Edge;
import soot.toolkits.graph.ExceptionalUnitGraph;
import soot.toolkits.graph.UnitGraph;

public class FlowPath {
	private int id; //-1 means not initialized.
	private ResultSinkInfo sink;
	private ResultSourceInfo source;
	
	private Stmt[] path;
	private List<Stmt> fullPath;
	private Map<String, Stmt> pathStmtMap;

	private Set<String> lifeCycleEventListenerSet = null;
	private Map<String, List<Stmt>> registryMap = null;
	private Set<String> declaringClassSet = null;
	private Set<String> allRelatedClassSet = null;
	private Set<String> allTrigerMethodSet = null;
	
	private IInfoflowCFG icfg;
	private CallGraph cg;
	private Pattern callbackMethodNamePatttern = Pattern.compile("^on[A-Z][a-z]");
	
	//TODO: fix this
	public SootMethod sinkMethod = null;
	/*** Constructors ***/
	public FlowPath(IInfoflowCFG icfg, ResultSourceInfo source, ResultSinkInfo sink,
			Set<String> lifeCycleEventListenerSet,
			Map<String, List<Stmt>> registryMap){
		long randomID = System.currentTimeMillis();
		NUDisplay.debug("Start creating new FlowPath "+randomID+": "+
				source.getSource()+"=>"+sink.getSink(), null);
		this.icfg = icfg;
		this.pathStmtMap = new HashMap<String, Stmt>();
		this.source = source;
		this.sink = sink;
		if(icfg != null)
			this.sinkMethod = icfg.getMethodOf(sink.getSink());
		this.cg =  Scene.v().getCallGraph();
		this.registryMap = registryMap;
		this.lifeCycleEventListenerSet = lifeCycleEventListenerSet;
		this.id = -1;
		this.declaringClassSet = new HashSet<String>();
		this.allTrigerMethodSet = new HashSet<String>();
		this.fullPath = new ArrayList<Stmt>();
		this.path = this.source.getPath();
		
		buildFullPath();
		NUDisplay.debug("Done creating FlowPath "+randomID+"\n", null);
	}
	
	public FlowPath(FlowPath sourceFP, FlowPath sinkFP){
		this.icfg = sourceFP.icfg;
		this.pathStmtMap = new HashMap<String, Stmt>();
		this.source = sourceFP.getSource();
		this.sink = sinkFP.getSink();
		if(icfg != null)
			this.sinkMethod = icfg.getMethodOf(sink.getSink());
		this.cg =  sourceFP.cg;
		this.registryMap = sourceFP.registryMap;
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
		
		buildFullPath();
	}
	
	/*** Public Methods ***/
	public Stmt findStmtFromFlowPath(Stmt s, InterproceduralCFG<Unit, SootMethod> newIcfg){
		return pathStmtMap.get(buildStmtSignature(s, newIcfg));
	}
	public String getSignature(){
		try{
			return buildStmtSignature(source.getSource(), icfg) + "=>" +
					buildStmtSignature(sink.getSink(), icfg);
		}
		catch(Exception e){
			return source.getSource() +"=>" +sink.getSink();
		}
	}
	public String getTag(){
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
	@Override
	public String toString(){
		StringBuilder sb = new StringBuilder();
		sb.append("PathBegin:\n");
		for(Stmt stmt : fullPath)
			sb.append("  "+stmt.toString()+"@"+icfg.getMethodOf(stmt)+"\n");
		sb.append("PathEnd:");
		return sb.toString();
	}
	@Override
	public int hashCode(){
		return getSignature().hashCode();
	}
	
	/*** Getters ***/
	public Set<String> getAllTrigerMethodSet() {
		return allTrigerMethodSet;
	}
	public Set<String> getDeclaringClassSet() {
		return declaringClassSet;
	}
	public Set<String> getAllRelatedClassSet(){
		return allRelatedClassSet;
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
	
	/*** Setters ***/
	public void setId(int id) {
		this.id = id;
	}
	
	/*** Private Methods ***/
	private void buildFullPath(){
		fullPath.add(source.getSource());
		//activition stmts
		List<Stmt> triggers = findActivationStmts(this.path);
		NUDisplay.debug("  Displaying activition stmts:"+triggers.size(), null);
		for(Stmt stmt : triggers){
			fullPath.add(stmt);
			NUDisplay.debug("    "+stmt, null);
		}
		//predicates
		List<Stmt> predicates = reconstructFlowPathPredicates(source.getPath());
		NUDisplay.debug("  Displaying predicates:"+triggers.size(), null);
		for(Stmt stmt : predicates){
			fullPath.add(stmt);
			NUDisplay.debug("    "+stmt+" @"+icfg.getMethodOf(stmt).getName(), null);
		}
		fullPath.add(sink.getSink());
		NUDisplay.debug("  Displaying fullpath:"+fullPath.size(), null);
		for(Stmt s : fullPath){
			pathStmtMap.put(buildStmtSignature(s, icfg), s);
			NUDisplay.debug("    "+icfg.getMethodOf(s).getName()+":"+s, null);
		}
		for(String cls : declaringClassSet){
			NUDisplay.debug("  Declaring Class: "+cls, null);
		}
		NUDisplay.debug("", null);
		allRelatedClassSet = findInvolvedClass(fullPath);
		for(String cls : allRelatedClassSet){
			NUDisplay.debug("  All Class: "+cls, null);
		}
		NUDisplay.debug("Done FlowPath: "+source.getSource()+"=>"+sink.getSink(), null);
	}
	
	private Set<String> findInvolvedClass(List<Stmt> path){
		Set<String> rs = new HashSet<String>();
		for(Stmt stmt : path){
			//SootMethod sm = icfg.getMethodOf(stmt);
			//rs.add(sm.getDeclaringClass().getName());
			Queue<Stmt> queue = new LinkedList<Stmt>();
			queue.add(stmt);
			Set<Stmt> visited = new HashSet<Stmt>();
			while(!queue.isEmpty()){
				Stmt s = queue.poll();
				if(visited.contains(s))
					continue;
				visited.add(s);
				SootMethod sm = icfg.getMethodOf(stmt);
				rs.add(sm.getDeclaringClass().getName());
				Collection<Unit> callers = icfg.getCallersOf(sm);
				for(Unit caller : callers){
					queue.add((Stmt)caller);
					
//					System.out.println("CALLGRAPH:"+sm+" calledby "+icfg.getMethodOf((Stmt)caller));
				}
			}
		}
		return rs;
	}
	
	private List<Stmt> findActivationStmts(Stmt[] path){
		List<Stmt> calbackRs = new ArrayList<Stmt>();
		List<Stmt> lifeCycleRs = new ArrayList<Stmt>();
		if(path == null || path.length==0)
			return calbackRs;
		
		for(int i=path.length-1; i>0; i--){
			Stmt cur = path[i];
			Stmt prev = path[i-1];
			
			SootMethod curMethod = icfg.getMethodOf(cur);
			SootMethod prevMethod = icfg.getMethodOf(prev);
			
			if(curMethod.getSignature().equals(prevMethod.getSignature()))
				continue;
			else {
				if(prev.containsInvokeExpr()){
					InvokeExpr ie = prev.getInvokeExpr();
					if(ie.getMethod().getSignature().equals(curMethod.getSignature())){
						allTrigerMethodSet.add(curMethod.getName());
						Matcher mat = callbackMethodNamePatttern.matcher(curMethod.getName());
						if(!this.lifeCycleEventListenerSet.contains(curMethod.getName()) && mat.find()){
							List<Stmt> lst = this.registryMap.get(curMethod.getDeclaringClass().toString());
							if(lst != null){
								for(Stmt s : lst)
									calbackRs.add(s);
							}
						}
						else if(this.lifeCycleEventListenerSet.contains(curMethod.getName())){
							List<Stmt> lst = this.registryMap.get(curMethod.getSignature());
							if(lst != null){
								for(Stmt s : lst)
									lifeCycleRs.add(s);
							}
							declaringClassSet.add(curMethod.getDeclaringClass().getName());
						}
						continue;			
					}
				}
			}
			
			//find caller of this stmt's methods
			findActivationStmtsHelper(curMethod, calbackRs, lifeCycleRs);
		}
		if(path.length > 0)
			findActivationStmtsHelper(icfg.getMethodOf(path[0]), calbackRs, lifeCycleRs);
		
		if(calbackRs.size() > 0)
			return calbackRs;
		else
			return lifeCycleRs;
	}
	
	private void findActivationStmtsHelper(SootMethod method, List<Stmt> calbackRs, List<Stmt> lifeCycleRs){
		if(this.icfg==null){
			NUDisplay.error("no icfg", "findActivationStmtsHelper");
			return;
		}
		if(method.getName().equals("dummyMainMethod"))
			return ;
		
		Queue<SootMethod> queue = new LinkedList<SootMethod>();
		Set<String> visited = new HashSet<String>();
		
		queue.add(method);
		visited.add(method.getSignature());
		
		while(!queue.isEmpty()){
			SootMethod sm = queue.poll();
			allTrigerMethodSet.add(sm.getName());
			Matcher mat = callbackMethodNamePatttern.matcher(sm.getName());
			if(!this.lifeCycleEventListenerSet.contains(sm.getName()) && mat.find()){
				List<Stmt> lst = this.registryMap.get(sm.getDeclaringClass().toString());
				if(lst != null){
					for(Stmt s : lst)
						calbackRs.add(s);
				}
			}
			else if(this.lifeCycleEventListenerSet.contains(sm.getName())){
				List<Stmt> lst = this.registryMap.get(sm.getSignature());
				if(lst == null) continue;
				for(Stmt s : lst)
					lifeCycleRs.add(s);
				declaringClassSet.add(sm.getDeclaringClass().getName());
			}
			else{
				Iterator<Edge> edges = cg.edgesInto(sm);
				//NUDisplay.debug("CGDEBUG: TARGET:"+sm.getSignature(), null);
				while(edges.hasNext()){
					Edge edge = edges.next();
					SootMethod predecessor = edge.getSrc().method();
					if(predecessor == null) continue;
					//NUDisplay.debug("  CGDEBUG: PARENT:"+predecessor.getSignature(), null);
					if(!visited.contains(predecessor.getSignature())){
						visited.add(predecessor.getSignature());
						queue.add(predecessor);
					}
				}
			}
		}
	}
	
	public List<Integer> findViewsInPaths(ISourceSinkManager mgr){
		List<Integer> rs = new ArrayList<Integer>();
		for(Stmt stmt : path){
			if(mgr.getSourceInfo(stmt, icfg) != null)
				rs.add(FlowPathSet.getViewIdFromStmt(stmt));
		}
		return rs;
	}
	
	private String buildStmtSignature(Stmt s, InterproceduralCFG<Unit, SootMethod> newIcfg){
		return ToolSet.createStmtSignature(s, (IInfoflowCFG)newIcfg);
	}
	
	private List<Stmt> reconstructFlowPathPredicates(Stmt[] path){
		List<Stmt> rs = new ArrayList<Stmt>();
		if(path == null || path.length==0)
			return rs;
		
		for(int i=path.length-1; i>0; i--){
			Stmt cur = path[i];
			if(cur instanceof ReturnVoidStmt)
				continue;
			Stmt prev = path[i-1];
			int j = i-2;
			while(prev instanceof ReturnVoidStmt){
				if(j < 0) break;
				prev = path[j--];
			}
			if(prev instanceof ReturnVoidStmt) break;
			
			addStmtToList(rs, cur);		
			SootMethod curMethod = icfg.getMethodOf(cur);
			SootMethod prevMethod = icfg.getMethodOf(prev);
			
			if(curMethod.getSignature().equals(prevMethod.getSignature())){
				Set<Stmt> subrs = addStmtIntraProcedure(curMethod, cur, prev);
				for(Stmt stmt : subrs)
					addStmtToList(rs, stmt);
			}
			else {
				if(prev.containsInvokeExpr()){
					InvokeExpr ie = prev.getInvokeExpr();
					if(ie.getMethod().getSignature().equals(curMethod.getSignature())){
						Set<Stmt> subrs = addStmtIntraProcedure(curMethod, cur, null);
						for(Stmt stmt : subrs)
							addStmtToList(rs, stmt);
					}
					else addStmtToList(rs, cur);
					
				}
				else addStmtToList(rs, cur);
			}
		}
		
		addStmtToList(rs, path[0]);
		Collections.reverse(rs);
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
	
	private void addStmtIntraProcedureHelper(UnitGraph g, Stmt cur, Stmt end, Set<Stmt> rs){
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

}
