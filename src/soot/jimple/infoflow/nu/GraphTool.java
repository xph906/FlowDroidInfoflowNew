package soot.jimple.infoflow.nu;

import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Queue;
import java.util.Set;
import java.util.Stack;

import soot.MethodOrMethodContext;
import soot.Scene;
import soot.SootMethod;
import soot.Unit;
import soot.UnitBox;
import soot.ValueBox;
import soot.jimple.BreakpointStmt;
import soot.jimple.DefinitionStmt;
import soot.jimple.IdentityStmt;
import soot.jimple.InvokeExpr;
import soot.jimple.MonitorStmt;
import soot.jimple.RetStmt;
import soot.jimple.ReturnStmt;
import soot.jimple.Stmt;
import soot.jimple.infoflow.solver.cfg.IInfoflowCFG;
import soot.toolkits.graph.ExceptionalUnitGraph;
import soot.toolkits.graph.UnitGraph;
import soot.util.queue.QueueReader;

public class GraphTool {
	static String outputFolder = "/tmp/";
	//static String outputFolder = "/Users/xpan/Documents/projects/dataflow-project/output/";
	static public void displayGraph(UnitGraph g, SootMethod m){
		String name = m.getName()+"-"+m.getDeclaringClass().getName();
		displayGraph(g, name, g.getHeads(), false);
	}
	static public void setOutputFolder(String dir){
		outputFolder = dir;
	}
	
	static public void displayAllMethodGraph(){
		for (QueueReader<MethodOrMethodContext> rdr =
				Scene.v().getReachableMethods().listener(); rdr.hasNext(); ) {
			SootMethod m = rdr.next().method();
			if(!m.hasActiveBody())
				continue;
			UnitGraph g = new ExceptionalUnitGraph(m.getActiveBody());
			displayGraph(g,m);
		}
	}
	
	static public void displayGraph(UnitGraph g, String graphName, List<Unit> startingUnits, boolean reverse) {
		PrintWriter writer = null;
		try{
			if (startingUnits == null)
				startingUnits = g.getHeads();
			String fileName = outputFolder+graphName+".txt";
			System.out.println("  Display graph "+graphName+" to "+fileName);
			writer = new PrintWriter(fileName, "UTF-8");
		    
			Stack<Pair<Unit, Integer>> queue = new Stack<Pair<Unit, Integer>>();
			Set<Unit> visitedUnits = new HashSet<Unit>();
			writer.println("DisplayGraph: " + graphName);
			for (Unit su : startingUnits) {
				if (!visitedUnits.contains(su)) {
					queue.add(new Pair<Unit, Integer>(su, 1));
					visitedUnits.add(su);
				}
			}
	
			while (!queue.isEmpty()) {
				Pair<Unit, Integer> item = queue.pop();
				String space = new String(new char[item.second * 2]).replace('\0', ' ');
				writer.println(space + item.first + " ");
				// if(item.second > 20)
				// break;
				List<Unit> next = (reverse ? g.getPredsOf(item.first) : g.getSuccsOf(item.first));
				for (Unit n : next) {
					if (!visitedUnits.contains(n)) {
						queue.add(new Pair<Unit, Integer>(n, item.second + 1));
						visitedUnits.add(n);
					}
				}
			}
			writer.println();
		}
		catch(Exception e){
			System.err.println("error in displayGraph: "+e.toString());
		}
		finally{
			if(writer != null)
				writer.close();
		}
	}
	
	static IInfoflowCFG icfg;
	
	public static List<List<Stmt>> buildFlowFullPath(IInfoflowCFG icfg, Stmt[] path){
		GraphTool.icfg = icfg;
		List<List<Stmt>> rs = new ArrayList<List<Stmt>>();
		for(int i=0; i<path.length-1; i++){
			Stmt cur = path[i];
			Stmt next = path[i+1];
			SootMethod curMethod = icfg.getMethodOf(cur);
			SootMethod nextMethod = icfg.getMethodOf(next);
			if(curMethod.getSignature().equals(nextMethod)){
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
//						for(List<Stmt> r : subrs)
//							for(Stmt s : r)
//								System.out.println("  DEBUG: "+s);
						addMultipleGroupStmtsToList(rs, subrs); //add stmts from the begining.
					}
					else 
						addOneStmtToList(rs, cur);
				}
				else { //TODO: get rid of RETURN stmt.
					addOneStmtToList(rs, cur);
				}
			}
		}
		addOneStmtToList(rs, path[path.length-1]);
		int cnt = 0;
		for(List<Stmt> lst : rs){
			System.out.println("Building Full Path: "+cnt+++" Size:"+lst.size());
			for(Stmt s : lst){
				List<ValueBox> boxes = s.getUseBoxes();
				System.out.println("  "+icfg.getMethodOf(s).getName()+":"+s);
				//for(ValueBox b : boxes)
				//	System.out.println("    "+b.getValue());
			}
		}
		return rs;
	}
	
	private static void addMultipleGroupStmtsToList(List<List<Stmt>> lst, List<List<Stmt>> adds){
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
	private static void addOneStmtToList(List<List<Stmt>> lst, Stmt stmt){
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
	private static void addStmtToList(List<Stmt> lst, Stmt stmt){
		if(stmt instanceof IdentityStmt || stmt instanceof BreakpointStmt ||
				stmt instanceof MonitorStmt || stmt instanceof RetStmt || 
				stmt instanceof ReturnStmt)
			return ;	
		for(Stmt s : lst)
			if(s.equals(stmt))
				return ;
			else if (s.toString().equals(stmt.toString())){
				System.out.println("Two Stmt equal based on string:");
				System.out.println("  :"+s+" VS "+stmt);
				
				boolean rs = icfg.getMethodOf(s).toString().equals(icfg.getMethodOf(stmt).toString());
				System.out.println("  method::"+rs+" "+icfg.getMethodOf(s)+" // "+icfg.getMethodOf(stmt));
				
			}
		lst.add(stmt);
	}
	
	private static List<List<Stmt>> addStmtIntraProcedure(SootMethod method, Stmt cur, Stmt end){
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
	
	private static void addStmtIntraProcedureHelper(UnitGraph g, Stmt cur, Stmt end, List<Stmt> curRS, List<List<Stmt>> rs, Set<Stmt> visited){
		//curRS remain the same when returned.
		if(cur.equals(end)){
			List<Stmt> newRS = new ArrayList<Stmt>();
			for(Stmt s : curRS)
				newRS.add(s);
			rs.add(newRS);
			return ;
		}
		
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
	
	public static void traverseICFGReversely(IInfoflowCFG icfg, Stmt start, Stmt end){
		List<List<Stmt>> rs = new ArrayList<List<Stmt>>();
		LinkedList<Stmt> workingLst = new LinkedList<Stmt>();
		workingLst.add(start);
		traverseHelper(icfg, end, workingLst, rs, new HashSet<Stmt>());
		
		System.out.println("XIANGPAN "+rs.size()+" path for flow:"+start+" "+end);
		int cnt = 0;
		for(List<Stmt> lst : rs){
			System.out.println("Begin path: "+cnt++);
			for(Stmt stmt : lst){
				System.out.println("  "+stmt);
			}
		}
	}
	private static void traverseHelper(IInfoflowCFG icfg, Stmt end, LinkedList<Stmt> workingLst, List<List<Stmt>> rs, Set<Stmt> visited){
		Stmt cur = workingLst.getFirst();
		if(cur.equals(end)){
			List<Stmt> curRs = new ArrayList<Stmt>();
			for(Stmt stmt : workingLst)
				curRs.add(stmt);
			rs.add(curRs);
			return ;
		}
		visited.add(cur);
		List<Unit> preds = icfg.getPredsOf(cur);
		System.out.println("DEBUG: "+cur);
		for(Unit pred : preds){
			System.out.println("  DEBUG: "+pred);
			Stmt stmt = (Stmt)pred;
			if(visited.contains(stmt)) continue;
			workingLst.addFirst(stmt);
			traverseHelper(icfg, end, workingLst, rs, visited);
			workingLst.removeFirst();
		}
		visited.remove(cur);
	}

	
	
}
