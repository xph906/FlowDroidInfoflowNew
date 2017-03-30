package soot.jimple.infoflow.nu;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Queue;
import java.util.Set;
import java.util.Stack;

import nu.NUDisplay;
import soot.Local;
import soot.MethodOrMethodContext;
import soot.PatchingChain;
import soot.Scene;
import soot.SootField;
import soot.SootMethod;
import soot.Unit;
import soot.UnitBox;
import soot.Value;
import soot.jimple.AnyNewExpr;
import soot.jimple.ArrayRef;
import soot.jimple.AssignStmt;
import soot.jimple.BinopExpr;
import soot.jimple.CastExpr;
import soot.jimple.Constant;
import soot.jimple.DefinitionStmt;
import soot.jimple.FieldRef;
import soot.jimple.IdentityStmt;
import soot.jimple.InstanceFieldRef;
import soot.jimple.InstanceInvokeExpr;
import soot.jimple.IntConstant;
import soot.jimple.InvokeExpr;
import soot.jimple.NewArrayExpr;
import soot.jimple.NewExpr;
import soot.jimple.NewMultiArrayExpr;
import soot.jimple.ParameterRef;
import soot.jimple.RetStmt;
import soot.jimple.ReturnStmt;
import soot.jimple.StaticFieldRef;
import soot.jimple.Stmt;
import soot.jimple.StringConstant;
import soot.jimple.ThisRef;
import soot.jimple.UnopExpr;
import soot.jimple.infoflow.solver.cfg.IInfoflowCFG;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.Edge;
import soot.jimple.toolkits.ide.icfg.BiDiInterproceduralCFG;
import soot.tagkit.IntegerConstantValueTag;
import soot.tagkit.StringConstantValueTag;
import soot.tagkit.Tag;
import soot.toolkits.graph.ExceptionalUnitGraph;
import soot.toolkits.graph.Orderer;
import soot.toolkits.graph.PseudoTopologicalOrderer;
import soot.toolkits.graph.UnitGraph;
import soot.util.queue.QueueReader;

public class ToolSet {
	static final String FIND_VIEW_BY_ID = "findViewById";
	static final String SET_CONTENT_VIEW = "setContentView";
	static final String SET_BACKGROUND_RESOURCE= "setBackgroundResource";
	static final String GET_IDENTIFIER_SIGNATURE = 
			"<android.content.res.Resources: int getIdentifier(java.lang.String,java.lang.String,java.lang.String)>";
	
	static IInfoflowCFG savedCFG = null;
	static CallGraph cg = null;
	static IResourceManager resMgr = null;
	public static void setICFG(IInfoflowCFG cfg){
		savedCFG = cfg;
		cg = Scene.v().getCallGraph();
	}
	
	public static void setResourceManager(IResourceManager mgr){
		resMgr = mgr;
	}
	
	public static String createStmtSignature(Stmt stmt, IInfoflowCFG cfg){
		if(cfg == null) cfg = savedCFG;
		if(cfg == null) return stmt.toString()+"@null";
	
		SootMethod curMethod = cfg.getMethodOf(stmt);
		if(curMethod == null)
			return stmt.toString()+"@null";
		else
			return stmt.toString()+"@"+curMethod.getSignature();
		
//		if(cfg == null)
//			cfg = savedCFG;
//		if(cfg == null){
//			NUDisplay.alert("creteStmtSignature use null cfg:"+stmt, "createStmtSignature");
//			return stmt.toString()+"@null@POSnull";
//		}
//		SootMethod sm = cfg.getMethodOf(stmt);
//		if(sm == null) return stmt.toString()+"@null@POSnull";
//		
//		String methodName = sm.getSignature();
//		StringBuilder sb = new StringBuilder();
//		sb.append(stmt.toString()+"@"+methodName+"@POS:");
//		if(!sm.hasActiveBody()){
//			sb.append("null");
//			return sb.toString();
//		}
//		PatchingChain<Unit> units = sm.getActiveBody().getUnits();
//		
//		//boolean found = false;
//		int cnt = 0;
//		for(Unit u : units){
//			cnt++;
//			if(stmt == u){
//				//found = true;
//				break;
//			}
//		}
//		
//	    sb.append(cnt);
//	    return sb.toString();
	}
	
	public static boolean isDynamicWidgetOrDialogSource(Stmt stmt){
		if(stmt instanceof DefinitionStmt){
			DefinitionStmt as = (DefinitionStmt)stmt;
			Value right = as.getRightOp();
			if(right instanceof NewExpr){
				String rightName = ((NewExpr)right).getType().getEscapedName();
				String[] elems = rightName.split("\\.");
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

	public static Integer findLastResIDAssignment(Stmt stmt, Value target, BiDiInterproceduralCFG<Unit, SootMethod> cfg, 
			Set<Stmt> visited, String methodName) {
		if(visited.contains(stmt)){
			return null;
		}
		visited.add(stmt);
		GlobalData gData = GlobalData.getInstance();
		if(cfg == null) {
			System.err.println("Error: findLastResIDAssignment cfg is not set.");
			return null;
		}
		// If this is an assign statement, we need to check whether it changes
		// the variable we're looking for
		if (stmt instanceof AssignStmt) {
			AssignStmt assign = (AssignStmt) stmt;
			if (assign.getLeftOp() == target) {
				System.out.println("  Debug: "+assign+" "+assign.getRightOp().getClass());
				// ok, now find the new value from the right side
				if (assign.getRightOp() instanceof IntConstant)
					return ((IntConstant) assign.getRightOp()).value;
				else if (assign.getRightOp() instanceof FieldRef) {
					SootField field = ((FieldRef) assign.getRightOp()).getField();
					for (Tag tag : field.getTags()){
						if (tag instanceof IntegerConstantValueTag){
							//System.out.println("This is an integerCOnstantValue");
							return ((IntegerConstantValueTag) tag).getIntValue();
						}
						else
							System.err.println("  Constant " + field + " was of unexpected type");
					}
					if(assign.getRightOp() instanceof InstanceFieldRef && 
							(!methodName.equals("setBackgroundResource"))){
						FieldRef fr = (FieldRef)assign.getRightOp();
						Integer id = resMgr.getResourceIdByName(fr.getFieldRef().name());
						if(id != null)
							return id;
						
						id = gData.getFieldID(fr.getField());
						if(id != null)
							return id;
					}
					if(assign.getRightOp() instanceof StaticFieldRef){
						StaticFieldRef sfr = (StaticFieldRef)assign.getRightOp();
						Integer id = resMgr.getResourceIdByName(sfr.getFieldRef().name());
						if(id != null)
							return id;
						
						if(gData.getFieldID(sfr.getField())!=null ){
							return gData.getFieldID(sfr.getField());
						}
						System.out.println("  Field not assigned:"+sfr);
						target = assign.getRightOp();
					}
				} 
				else if(assign.getRightOp() instanceof Local){
					target = assign.getRightOp();
				}
				else if (assign.getRightOp() instanceof InvokeExpr) {
					InvokeExpr inv = (InvokeExpr) assign.getRightOp();
					if (inv.getMethod().getName().equals("getIdentifier") && 
							inv.getMethod().getDeclaringClass().getName().equals("android.content.res.Resources") 
							&& resMgr.resourcePakcageSize() >= 0) {
						// The right side of the assignment is a call into the
						// well-known
						// Android API method for resource handling
						if (inv.getArgCount() != 3) {
							System.err.println("Invalid parameter count for call to getIdentifier:"+inv.getArgCount());
							return null;
						}

						// Find the parameter values
						String resName = "";
						String resID = "";
						String packageName = "";

						// In the trivial case, these values are constants
						if (inv.getArg(0) instanceof StringConstant)
							resName = ((StringConstant) inv.getArg(0)).value;
						if (inv.getArg(1) instanceof StringConstant)
							resID = ((StringConstant) inv.getArg(1)).value;
						if (inv.getArg(2) instanceof StringConstant)
							packageName = ((StringConstant) inv.getArg(2)).value;
						else if (inv.getArg(2) instanceof Local)
							packageName = ToolSet.findLastResStringAssignment(stmt, (Local) inv.getArg(2), cfg, new HashSet<Stmt>());
						else {
							if(inv.getArg(0) instanceof Local){
								GraphTool.displayGraph(new ExceptionalUnitGraph(cfg.getMethodOf(assign).getActiveBody()), cfg.getMethodOf(assign));
								String key = ToolSet.findLastResStringAssignment(stmt, (Local)inv.getArg(0), cfg,  new HashSet<Stmt>());
								
								if(key !=null && key.length()>0)
									return resMgr.getResourceIdByName(key);
							}
							System.err.println("Unknown parameter type in call to getIdentifier: "+inv.getArg(0));
							return null;
						}

						// Find the resource
						Integer id  = resMgr.getResourceId(resName, resID, packageName);
						if(id != null) return id;
					}
					else if((inv.getMethod().getName().startsWith("get") || inv.getMethod().getName().equals("id") ) && 
							inv.getArgCount()>=1 && inv.getArg(0) instanceof StringConstant && 
							inv.getMethod().getReturnType().getEscapedName().equals("int")){
						System.out.println("ReturnType:"+inv.getMethod().getReturnType().getEscapedName().equals("int"));
						if(inv.getArgCount() < 1) return null;
						String resName = "";
						if (inv.getArg(0) instanceof StringConstant)
							resName = ((StringConstant) inv.getArg(0)).value;
						if(!resName.equals("")){
							return resMgr.getResourceIdByName(resName);
						}
					}
					else if(inv.getMethod().getName().equals("getId") && 
							inv.getMethod().getDeclaringClass().getName().equals("com.playhaven.android.compat.VendorCompat") ){
						//com.playhaven.android.compat.VendorCompat: int getId(android.content.Context,com.playhaven.android.compat.VendorCompat$ID)
						Value v = inv.getArg(1);
						if(v instanceof Local){
							Value vv = findFirstLocalDef(assign, (Local)v, cfg);
							if(vv!=null && vv instanceof StaticFieldRef){
								Integer id = resMgr.getResourceIdByName(((StaticFieldRef)vv).getField().getName());
								if(id != null)
									return id;
							}
						}
					}
					else if(inv.getArgCount()>=1 && inv.getMethod().getReturnType().getEscapedName().equals("int")){
						for(Value arg : inv.getArgs()){
							if(arg instanceof StringConstant){
								String key = ((StringConstant) arg).value;
								Integer id = resMgr.getResourceIdByName(key);
								if(id != null)
									return id;
							}
						}
					}
					else if(inv.getArgCount()>=1 && inv.getMethod().getName().equals("inflate") ){
						Value arg = inv.getArg(0);
						if(arg instanceof Local)
							target = arg;
						else if(arg instanceof IntConstant)
							return ((IntConstant) arg).value;
					}
					else{
						try{
						GraphTool.displayGraph(new ExceptionalUnitGraph(inv.getMethod().getActiveBody()), inv.getMethod());
						}
						catch(Exception e){}
					}
					
				}
			}
			
		}
		else if(stmt instanceof IdentityStmt){
			IdentityStmt is = (IdentityStmt)stmt;
			if(is.getLeftOp() == target){
				System.out.println("From IdentityStmt: "+is);
				if(is.getRightOp() instanceof ParameterRef){
					ParameterRef right = (ParameterRef)(is.getRightOp());
					int idx = right.getIndex();
					Collection<Unit> callers = cfg.getCallersOf(cfg.getMethodOf(stmt));
					if(callers != null && callers.size()>0){
						for(Unit caller : callers){
							System.out.println("  Caller: From IdentityStmt: "+caller);
							InvokeExpr ie = ((Stmt)caller).getInvokeExpr();
							if(idx >= ie.getArgCount())
								continue;
							Value arg = ie.getArg(idx);
							if(arg instanceof IntConstant)
								return ((IntConstant) arg).value;
							else{
								System.out.println("Still not integer");
								Integer lastAssignment = findLastResIDAssignment((Stmt) caller, arg, cfg, visited, methodName);
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
			Integer lastAssignment = findLastResIDAssignment((Stmt) pred, target, cfg, visited, methodName);
			if (lastAssignment != null)
				return lastAssignment;
		}
		return null;
	}
	
	public static String findLastResStringAssignment(Stmt stmt, Value target, 
			BiDiInterproceduralCFG<Unit, SootMethod> cfg, Set<Stmt> visited) {
		if(visited.contains(stmt)){
			return null;
		}
		visited.add(stmt);
		
		if(cfg == null) {
			NUDisplay.error("findLastResIDAssignment cfg is not set.","findLastResStringAssignment");
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
	
	public static List<Stmt> searchVariableDefs(UnitGraph g, Stmt s, Value target, List<List<Object>> args, SootMethod m){
		assert(cg != null);
		List<Stmt> rs = new ArrayList<Stmt>();
		Queue<Unit> queue = new LinkedList<Unit>();
		Set<Unit> visited = new HashSet<Unit>();
		queue.add(s);
		
		while(!queue.isEmpty()){
			Stmt pred = (Stmt)queue.poll();
			visited.add(pred);
			boolean cont = true;
			if(pred instanceof AssignStmt){
				AssignStmt as = (AssignStmt)pred;
				if(as.getLeftOp().equals(target)){
					Value right = as.getRightOp();
					cont = false;
					System.out.println("  -"+as+" "+right.getClass());
					if(right instanceof CastExpr){
						System.out.println("  DEBUG: this is cast expr: "+right);
						target = ((CastExpr) right).getOp();
					}
					else if(right instanceof BinopExpr ||
							right instanceof UnopExpr){
						System.out.println("  DEBUG: this is binop/unop expr: "+right);
					}
					else if(right instanceof AnyNewExpr ||
							right instanceof NewArrayExpr ||
							right instanceof NewExpr ||
							right instanceof NewMultiArrayExpr){
						System.out.println("  DEBUG: this is new expr: "+right);
					}
					else if(right instanceof InvokeExpr){
						System.out.println("  DEBUG: this is invoke expr: "+right);
						InvokeExpr nie = (InvokeExpr)right;
						if(nie.getArgCount()>0){
							List<Object> newArgs = new ArrayList<Object>();
							for(int i=0; i<nie.getArgCount(); i++){
								Value arg = nie.getArg(i);
								if(arg instanceof StringConstant){
									StringConstant sc = (StringConstant)arg;
									newArgs.add(sc.value);
								}
								else if(arg instanceof Constant){
									newArgs.add(arg);
								}
							}
							args.add(newArgs);
						}
						UnitGraph targetGraph = findMethodGraph(nie.getMethod());
						if(targetGraph == null){
							if(nie.getMethod().getSignature().equals(GET_IDENTIFIER_SIGNATURE)){
								//System.out.println(nie.getMethod().getSignature());
								if(args.size()>0)
									handleGetIdentifierCase(args.get(0));
								else
									System.out.println("No args stored for getIndetifier");
							}
							else{
								System.out.println("  ALERT: no body: "+nie.getMethod());
							}
						}
						else{
							//GraphTool.displayGraph(targetGraph, nie.getMethod());
							List<Unit> tails = targetGraph.getTails();
							for(Unit t : tails){
								if(t instanceof RetStmt){//No use case
									RetStmt retStmt = (RetStmt)t;
									//System.out.println("  RetVal:"+retStmt.getStmtAddress());
									searchVariableDefs(targetGraph, (Stmt)t, retStmt.getStmtAddress(),args, nie.getMethod());
								}
								else if(t instanceof ReturnStmt){
									ReturnStmt returnStmt = (ReturnStmt)t;
									//System.out.println("  ReturnVal:"+returnStmt.getOp());
									searchVariableDefs(targetGraph, (Stmt)t, returnStmt.getOp(),args, nie.getMethod());
								}
							}
							//searchVariableDefs(g, s, v);
						}
					}
					else{
						if(right instanceof StaticFieldRef){
							try{
								StaticFieldRef sfr = (StaticFieldRef)right;
								
								searchStaticVariable(sfr);
							}
							catch(Exception e){
								System.out.println("Error converting NumbericConstant to int: "+e+" "+right);
							}
							
						}
						else if(right instanceof FieldRef){
							//TODO: regular field
							System.out.println("  DEBUG: this is other expr: "+right.getClass());
						}
						else{
							System.out.println("  DEBUG: this is other expr: "+right.getClass());
						}
					}
			
					rs.add(as);
				}
				
			}
			else if(pred instanceof IdentityStmt){
				System.out.println("  DEBUG: this is IdentityStmt: ");
				Iterator<Edge> edges = cg.edgesInto(m);
				while(edges.hasNext()){
					Edge edge = edges.next();
					MethodOrMethodContext mmc = edge.getSrc();
					System.out.println("    CalledBy:"+mmc.method().getSignature());
					//GraphTool.displayGraph(findMethodGraph(mmc.method()), mmc.method());
				}
			}
			
			if(cont){
				List<Unit> preds = g.getPredsOf(pred);
				for(Unit p : preds){
					if(visited.contains(p)) continue;
					queue.add(p);
				}
			}
		}
		return rs;
	}
	
	public static void findViewDefStmt(Stmt stmt, Value target, List<NUAccessPath> bases,
			BiDiInterproceduralCFG<Unit, SootMethod> cfg, Set<Stmt> visited, Set<Stmt> rs){
		long startingTime = System.currentTimeMillis();
		long timeDiffSeconds = 0;
		
		if(visited.contains(stmt))
			return ;
		if(cfg == null){
			NUDisplay.error("Error: findViewDefStmt: cfg is not set", null);
			return ;
		}
		
		Stack<Stmt> stack = new Stack<Stmt>();
		stack.add(stmt);
		
		while(!stack.isEmpty()){
			timeDiffSeconds = (System.currentTimeMillis() - startingTime)/1000;
			if(timeDiffSeconds > 300){//5mins
				NUDisplay.error("passed time diff: "+timeDiffSeconds, null);
				continue ;
			}
			
			stmt = stack.pop();
			visited.add(stmt);
			
			if(stmt instanceof AssignStmt){
				AssignStmt as = (AssignStmt)stmt;
				if(sameValue(as.getLeftOp(),target) ){
					findViewDefStmtHelper(as, target, bases, cfg, visited, rs);
					continue ;
				}
				else if(target instanceof InstanceFieldRef){ //as.getLeftOp() != target
					//if left != right, we only care if target is InstanceFieldRef
					//because its possible a different Value points to target (alias)
					Value left = as.getLeftOp();
					if(pointToSameValue(left, target, bases)){
						findViewDefStmtHelper(as, target, bases, cfg, visited, rs);	
						continue ;
					}
					
					//left op doesn't point to the target
					//check if left is a prefix of one of bases
					if (!as.containsInvokeExpr() && NUAccessPath.containsAccessPathWithPrefix(bases, left)){
						List<NUAccessPath> lst= NUAccessPath.findAccessPathWithPrefix(bases, left);
						for(NUAccessPath ap : lst)
							ap.replacePrefix(left, as.getRightOp());
					}
					else if(NUAccessPath.containsAccessPathWithPrefix(bases, left)){
						List<NUAccessPath> lst= NUAccessPath.findAccessPathWithPrefix(bases, left);
						InvokeExpr ie = stmt.getInvokeExpr();
						SootMethod sm = null;
						if(ie != null) sm = ie.getMethod();
						if(sm!=null && sm.hasActiveBody()){
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
									NUDisplay.alert("not ends with ret stmt"+u.getClass()+"  "+u, 
											"findViewDefStmt");
								}
							}
							
						}// sm.hasActiveBody
						
						for(NUAccessPath ap : lst)
							bases.remove(ap);
						if(bases == null)
							continue ;
					}
				}
			}
			else if(stmt instanceof IdentityStmt){
				IdentityStmt is = (IdentityStmt)stmt;
				//left value is target or left value is a prefix of target
				if(pointToSameValue( is.getLeftOp(),target, bases) || 
					(target instanceof InstanceFieldRef && NUAccessPath.containsAccessPathWithPrefix(
								bases, ((IdentityStmt) stmt).getLeftOp()))){
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
									findViewDefStmt((Stmt) caller, target, newBases, cfg, newVisited, rs);
								}
							}
						}
					}
					else if(is.getRightOp() instanceof ThisRef){
						if(pointToSameValue(is.getLeftOp(),target, bases)){
							NUDisplay.alert("shouldn't come here findViewDefStmt 1", "findViewDefStmt");
							continue;
						}
						try{
							List<SootMethod> methods = cfg.getMethodOf(stmt).getDeclaringClass().getMethods();
							for(SootMethod method : methods){
								if(method == cfg.getMethodOf(stmt)) continue;
								if(!method.hasActiveBody()) continue;
								UnitGraph g = new ExceptionalUnitGraph(method.getActiveBody());
							    for(Unit u : g.getTails()){
							    	List<NUAccessPath> tmpBases = new ArrayList<NUAccessPath>();
									List<NUAccessPath> fitBases = NUAccessPath.findAccessPathWithPrefix(bases, is.getLeftOp());
									for(NUAccessPath np: fitBases)
										tmpBases.add(new NUAccessPath(np));
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
							NUDisplay.error("shouldn't come here findViewDefStmt 1", "findViewDefStmt");
						}
					}
					continue ;
				}
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
				if(visited.contains(pred))
					continue;
				//TODO: ideally, the newVisited should be reset for each predecessor, but it's too slow...
				stack.add((Stmt)pred);
			}	
		}
	}
	
	
	/*** Private methods ***/

	private static UnitGraph findMethodGraph(SootMethod method){
		for (QueueReader<MethodOrMethodContext> rdr =
				Scene.v().getReachableMethods().listener(); rdr.hasNext(); ) {
			SootMethod m = rdr.next().method();
			if(!m.hasActiveBody())
				continue;
			if(m.equals(method)){
				UnitGraph g = new ExceptionalUnitGraph(m.getActiveBody());
				return g;
			}
		}
		return null;
	}
	private static void searchStaticVariable(StaticFieldRef sfr){
		System.out.println("Start search static variable: "+sfr);
		for (QueueReader<MethodOrMethodContext> rdr =
				Scene.v().getReachableMethods().listener(); rdr.hasNext(); ) {
			SootMethod m = rdr.next().method();
			if(!m.hasActiveBody()) continue;
			
			UnitGraph g = new ExceptionalUnitGraph(m.getActiveBody());
		    Orderer<Unit> orderer = new PseudoTopologicalOrderer<Unit>();
		    for (Unit u : orderer.newList(g, false)) {
		    	Stmt s = (Stmt)u;
		    	if(s instanceof AssignStmt){
		    		AssignStmt as = (AssignStmt)s;
		    		Value left = as.getLeftOp();
		    		if(left instanceof StaticFieldRef){
		    			StaticFieldRef ls = (StaticFieldRef)left;
		    			if(ls.getField().equals(sfr.getField().getName())  && 
		    					ls.getFieldRef().declaringClass().getName().equals(sfr.getFieldRef().declaringClass().getName())){
			    			System.out.println("  SEARCH_STATIC_VARIABLE:"+as+" ||"+sfr.getField().getName());
			    		}
			    		else{
			    			//System.out.println("");
			    		}
		    		}
		    	}
		    }
		}
	}
	private static void handleGetIdentifierCase(List<Object> args){
		for(int i=0; i<args.size(); i++){
			if(!(args.get(i) instanceof String))
				continue;
			String arg = (String)args.get(i);
			Integer id = resMgr.getResourceIdByName(arg);
			if(id != null){
				System.out.println("FOUND ID of "+args.get(i)+" "+id);
			}
		}
	}
	private static Value findFirstLocalDef(Stmt sp, Local target, BiDiInterproceduralCFG<Unit, SootMethod> cfg){
		Set<Unit> visited = new HashSet<Unit>();
		Queue<Unit> queue = new LinkedList<Unit>();
		queue.add(sp);
		while(!queue.isEmpty()){
			Stmt stmt = (Stmt)queue.poll();
			visited.add(stmt);
			if(stmt instanceof AssignStmt){
				if(((AssignStmt) stmt).getLeftOp() == target){
					Value right = ((AssignStmt) stmt).getRightOp();
					System.out.println(" found an def of target: "+right+" ?//"+right.getClass());
					return right;
				}
			}
			for (Unit pred : cfg.getPredsOf(stmt)) {
				if (!(pred instanceof Stmt))
					continue;
				if(!visited.contains(pred))
					queue.add(pred);
			}
		}
		return null;
	}
	
	private static void findViewDefStmtHelper(AssignStmt stmt,  Value target, List<NUAccessPath> bases,
			BiDiInterproceduralCFG<Unit, SootMethod> cfg, Set<Stmt> visited, Set<Stmt> rs){
		//either isSame(target, stmt.getLeftOp()) or 
		//target.fieldName==stmt.getLeftOp().fieldName && NUAccessPath.containsAccessPath(bases, stmt.getLeftOp().getBase())
		Value right = stmt.getRightOp();
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
	private static boolean sameValue(Value left, Value right){
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
	private static boolean pointToSameValue(Value candidate, Value target, List<NUAccessPath> bases){
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
	

	/*The following methods can be deleted.*/
	public static void displayMethod(SootMethod sm){
		PatchingChain<Unit> units = sm.getActiveBody().getUnits();
		int cnt = 0;
		for(Unit u : units){
			cnt++;
			System.out.print(cnt+":"+u+", ");
			if(cnt%5==0)
				System.out.println();
		}
	}
	public static Set<String> extractFindViewById(){
		Set<String> set = new HashSet<String>();
		int cnt = 0;
		for (QueueReader<MethodOrMethodContext> rdr =
				Scene.v().getReachableMethods().listener(); rdr.hasNext(); ) {
			SootMethod m = rdr.next().method();
			if(!m.hasActiveBody())
				continue;
			if(m.getName().contains("dummyMainMethod"))
				ToolSet.displayMethod(m);
			UnitGraph g = new ExceptionalUnitGraph(m.getActiveBody());
		    Orderer<Unit> orderer = new PseudoTopologicalOrderer<Unit>();
		    for (Unit u : orderer.newList(g, false)) {
		    	cnt++;
		    	Stmt s = (Stmt)u;
		    	if(s.containsInvokeExpr()){
		    		InvokeExpr ie = s.getInvokeExpr();
		    		if(ie.getMethod().getName().contains("<init>")){
		    			set.add(ToolSet.createStmtSignature(s, null));
		    		}
		    	}
		    }
		 }
		System.out.println("THERE ARE "+cnt+" STMTs 1");
		return set;
	}
	public static void verifyFindViewById(Set<String> testx){
		int cnt = 0, cnt2=0;
		for (QueueReader<MethodOrMethodContext> rdr =
				Scene.v().getReachableMethods().listener(); rdr.hasNext(); ) {
			SootMethod m = rdr.next().method();
			if(!m.hasActiveBody())
				continue;

			if(m.getName().contains("dummyMainMethod"))
				ToolSet.displayMethod(m);
			UnitGraph g = new ExceptionalUnitGraph(m.getActiveBody());
		    Orderer<Unit> orderer = new PseudoTopologicalOrderer<Unit>();
		    for (Unit u : orderer.newList(g, false)) {
		    	Stmt s = (Stmt)u;
		    	cnt2++;
		    	if(s.containsInvokeExpr()){
		    		InvokeExpr ie = s.getInvokeExpr();
		    		String sig = ToolSet.createStmtSignature(s, null);
		    		if(ie.getMethod().getName().contains("<init>")){
		    			if(testx.contains(sig)) cnt++;
		    			else {
		    				System.out.println("MISSINGONE: "+sig);
		    			}
		    		}
		    	}
		    }
		 }
		System.out.println("TESTRESULT:"+cnt+" vs "+testx.size());
		System.out.println("THERE ARE "+cnt2+" STMTs21");
	}
}
