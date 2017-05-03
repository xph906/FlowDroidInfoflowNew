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
import soot.jimple.InvokeStmt;
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
	static long cfgStartingTime = 0;
	public static void setICFG(IInfoflowCFG cfg){
		savedCFG = cfg;
		cg = Scene.v().getCallGraph();
	}
	
	public static void setResourceManager(IResourceManager mgr){
		resMgr = mgr;
	}
	
	public static String createStmtSignatureWithMethod(Stmt stmt, SootMethod sm){
		if(sm == null) 
			return stmt.toString() + "@null";
		else
			return stmt.toString()+"@"+sm.getSignature();
	}
	
	public static String createStmtSignature(Stmt stmt, IInfoflowCFG cfg){
		if(cfg == null) cfg = savedCFG;
		if(cfg == null) return stmt.toString()+"@null";
	
		SootMethod curMethod = cfg.getMethodOf(stmt);
		if(curMethod == null)
			return stmt.toString()+"@null";
		
		return createStmtSignatureWithMethod(stmt, curMethod);
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
	
	public static boolean isInternetSinkStmt(Stmt s){
		if(!s.containsInvokeExpr())
			return false;
		InvokeExpr ie = s.getInvokeExpr();
		String clsName = null;
		SootMethod sm = null;
		try{
			sm = ie.getMethod();
			clsName = sm.getDeclaringClass().getName();
		}
		catch(Exception e){
			NUDisplay.error(e.toString(),"isInternetSinkStmt");
		}
		if(sm==null || clsName==null)
			return false;
		if(clsName.equals("org.apache.http.impl.client.DefaultHttpClient") && sm.getName().equals("execute"))
			return true;
		else if(clsName.equals("org.apache.http.client.HttpClient") && sm.getName().equals("execute"))
			return true;
		else if(clsName.equals("java.net.URL") && sm.getName().equals("<init>"))
			return true;
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
						else if (inv.getArg(2) instanceof Local){
							List<String> tmp= ToolSet.findLastResStringAssignment(stmt, (Local) inv.getArg(2), cfg, new HashSet<Stmt>());
							if(tmp!=null && tmp.size()>0)
								packageName = tmp.get(0);
						}
						else {
							if(inv.getArg(0) instanceof Local){
								GraphTool.displayGraph(new ExceptionalUnitGraph(cfg.getMethodOf(assign).getActiveBody()), cfg.getMethodOf(assign));
								List<String> tmp = ToolSet.findLastResStringAssignment(stmt, (Local)inv.getArg(0), cfg,  new HashSet<Stmt>());
								String key = null;
								if(tmp!=null && tmp.size()>0)
									key = tmp.get(0);
								
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
	public static String findLastResStringAssignmentSingle(Stmt stmt, Value target, 
			BiDiInterproceduralCFG<Unit, SootMethod> cfg, Set<Stmt> visited){
		setCFGStartingTime();
		List<String> rs = findLastResStringAssignment(stmt, target, cfg, visited);
		
		if(rs==null || rs.size()==0)
			return null;
		else{
			StringBuilder sb = new StringBuilder();
			for(String str : rs)
				if(!str.startsWith("[NUTAG]"))
					sb.append(str+", ");
			return sb.toString();
		}
	}
	public static String findLastResStringAssignmentAccurate(Stmt stmt, Value target, 
			BiDiInterproceduralCFG<Unit, SootMethod> cfg, Set<Stmt> visited){
		setCFGStartingTime();
		List<String> rs = findLastResStringAssignment(stmt, target, cfg, visited);
		if(rs==null || rs.size()==0)
			return null;
		else{
			for(String str : rs)
				if(!str.startsWith("[NUTAG]"))
					return str;
			return rs.get(0);
		}
	}
	//String starts with [NUTAG] is created by us.
	public static List<String> findLastResStringAssignment(Stmt stmt, Value target, 
			BiDiInterproceduralCFG<Unit, SootMethod> cfg, Set<Stmt> visited) {
		long timeDiffSeconds = (System.currentTimeMillis() - cfgStartingTime)/1000;
		if(timeDiffSeconds > 300){//5mins
			//NUDisplay.error("passed time diff: "+timeDiffSeconds, null);
			return new ArrayList<String>();
		}
		if(visited.contains(stmt)){
			NUDisplay.error("visited", "findLastResStringAssignment");
			return null;
		}
		if(cfg == null) {
			NUDisplay.error("findLastResIDAssignment cfg is not set.","findLastResStringAssignment");
			return null;
		}
		boolean debug = false;
		List<String> rs = new ArrayList<String>();
		Queue<Stmt> queue = new LinkedList<Stmt>();
		queue.add(stmt);
		// If this is an assign statement, we need to check whether it changes
		// the variable we're looking for
		while(!queue.isEmpty()){
			if(rs.size() > 20) 
				return rs;
			stmt = queue.poll();
			//if(debug) NUDisplay.debug("DEBUG: "+stmt+" "+target+", "+visited.contains(stmt), null);
			
			if(visited.contains(stmt))
				continue;
			visited.add(stmt);
			if (stmt instanceof AssignStmt) {
				AssignStmt assign = (AssignStmt) stmt;
				Value left = assign.getLeftOp();
				if (assign.getLeftOp() == target || 
						((left instanceof ArrayRef) && (((ArrayRef)left).getBase()==target)) ||
						((target instanceof ArrayRef) && (((ArrayRef)target).getBase()==left)) ||
						((left instanceof ArrayRef) &&  (target instanceof ArrayRef) && (((ArrayRef)target).getBase()==((ArrayRef)left).getBase()))) {
					//NUDisplay.debug("  analyze stmt:"+stmt+" FOR["+target +"] @"+cfg.getMethodOf(stmt).getSignature(), "findLastResStringAssignment");
					// ok, now find the new value from the right side
					if (assign.getRightOp() instanceof StringConstant) {
						rs.add(((StringConstant) assign.getRightOp()).value);
						continue;
					} 
					else if(assign.getRightOp() instanceof AnyNewExpr){
						//NUDisplay.debug("  *** target is new."+stmt, null);
						continue;
					}
					else if(assign.getRightOp() instanceof ArrayRef){
						target = assign.getRightOp();
					}
					else if (assign.getRightOp() instanceof FieldRef) {
						Value v = findStringHelperHandleFieldRef((FieldRef)assign.getRightOp(), stmt, rs, cfg, visited);
						if(v == null) 
							continue;
						else target = v;
					} 
					else if(assign.getRightOp() instanceof Local){
						target = assign.getRightOp();
					}
					else if(assign.getRightOp() instanceof CastExpr){
						target = assign.getRightOp();
					}
					else if (assign.getRightOp() instanceof InvokeExpr) {
						NUDisplay.debug("  findLastResStringAssignment right invoke expr:"+assign, null);
						InvokeExpr ie = (InvokeExpr)assign.getRightOp();
						if(ie.getArgCount()==0 && ie.getMethod().hasActiveBody()){
							findStringHelperHandleNonParamMethod(ie, rs, cfg, visited);
							continue;
						}
						else if(ie.getMethod().getName().equals("format") && 
								ie.getMethod().getDeclaringClass().getName().equals("java.lang.String")){
							findStringHelperHandleFormatMethod(ie,stmt, rs, cfg, visited);
							continue;
						}
						else if((ie.getMethod().getName().equals("replace") ||
								ie.getMethod().getName().equals("replaceAll") || 
								ie.getMethod().getName().equals("replaceFirst")) && 
								ie.getMethod().getDeclaringClass().getName().equals("java.lang.String")){
							try{
								target = ((InstanceInvokeExpr)ie).getBase();
								Value arg = ie.getArg(1);
								if(arg instanceof Constant)
									rs.add(arg.toString());
								else{
									Set<Stmt> newVisited = new HashSet<Stmt>();
									newVisited.addAll(visited);
									for (Unit pred : cfg.getPredsOf(assign)) {
										if (!(pred instanceof Stmt))
											continue;
										if(visited.contains(pred))
											continue;
										
										List<String> subrs = findLastResStringAssignment((Stmt) pred, arg, cfg, newVisited);
										if(subrs != null)
											for(String t : subrs)
												rs.add(t);
									}
								}
							}
							catch(Exception e){
								NUDisplay.alert("java.net.URL is not instance invoke expr:"+stmt, "findLastResStringAssignment");
							}
						}
						else if(ie.getMethod().getDeclaringClass().getName().equals("java.net.URL") ||
								ie.getMethod().getDeclaringClass().getName().equals("android.net.Uri")){
							try{
								target = ((InstanceInvokeExpr)ie).getBase();
								//debug = true;
								//GraphTool.displayGraph(new ExceptionalUnitGraph(cfg.getMethodOf(assign).getActiveBody()), cfg.getMethodOf(assign));
							}
							catch(Exception e){
								NUDisplay.alert("java.net.URL is not instance invoke expr:"+stmt, "findLastResStringAssignment");
							}
						}
						else if(ie.getMethod().getName().equals("toString")){
							try{
								target = ((InstanceInvokeExpr)ie).getBase();
								//debug = true;
								//GraphTool.displayGraph(new ExceptionalUnitGraph(cfg.getMethodOf(assign).getActiveBody()), cfg.getMethodOf(assign));
							}
							catch(Exception e){
								NUDisplay.alert("StringBuilder.toString is not instance invoke expr:"+stmt, "findLastResStringAssignment");
								continue;
							}
						}
						else if(ie.getMethod().getName().equals("append") &&
								ie.getMethod().getDeclaringClass().getName().equals("java.lang.StringBuilder")){
							findStringHelperHandleAppendMethod(ie,stmt, rs, cfg, visited);
							continue;
						}
						else if(ie.getMethod().hasActiveBody()){
							findStringHelperHandleRegularMethod(ie,stmt, rs, cfg, visited);
							continue;
						}
						else if(!ie.getMethod().getReturnType().toString().equals("java.lang.String")){
							NUDisplay.alert("ignore ie:"+ie.getMethod().getReturnType().toString(), null);
							continue;
						}
						else if(ie.getMethod().getName().equals("encode") && ie.getArgCount()>0){
							Value arg = ie.getArg(0);
							if(arg instanceof StringConstant){
								rs.add(((StringConstant) arg).value);
								continue;
							}
							else if(arg instanceof Constant){
								rs.add(arg.toString());
								continue;
							}
							target = arg;
						}
						else if(ie.getMethod().getName().equals("toUpperCase") || ie.getMethod().getName().equals("toLowerCase")){
							try{
								target = ((InstanceInvokeExpr)ie).getBase();
							}
							catch(Exception e){
								NUDisplay.alert("StringBuilder.toUpperCase/toLowerCase is not instance invoke expr:"+stmt, "findLastResStringAssignment");
								continue;
							}
						}
						else if(ie.getMethod().getDeclaringClass().getName().equals("org.apache.http.message.BasicNameValuePair")){
							try{
								target = ((InstanceInvokeExpr)ie).getBase();
//								NUDisplay.debug("Found a basicNameValuePair:"+ie, null);
							}catch(Exception e){
								continue;
							}
						}
						else{
//							NUDisplay.alert("  string return val:"+ie.getMethod().getReturnType().toString(), null);
//							NUDisplay.debug("  Cannot do inter-procedure analysis:"+ie, null);
							rs.add("[NUTAG] <METHODCALL>:"+ie.getMethod().getSignature());
							continue;
						}
						
					}//left==target and right is InvokeExpr
				}
				else if( (assign.getRightOp() instanceof InvokeExpr) && 
						(assign.getInvokeExpr().getMethod().getName().equals("append")) &&
						(assign.getInvokeExpr().getMethod().getDeclaringClass().getName().equals("java.lang.StringBuilder"))){
					Value base = ((InstanceInvokeExpr)(assign.getInvokeExpr())).getBase();
					if(base == target)
						findStringHelperHandleAppendMethod(assign.getInvokeExpr(), stmt, rs, cfg, visited);
				}
			}
			else if(stmt instanceof IdentityStmt){
				IdentityStmt is = (IdentityStmt)stmt;
				if(is.getLeftOp() == target){
					//NUDisplay.debug("  IdentityStmt analyze stmt:"+stmt+" FOR["+target +"] @"+cfg.getMethodOf(stmt).getSignature(), "findLastResStringAssignment");
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
									rs.add(((StringConstant) arg).value);
								else{
									List<String> subrs = findLastResStringAssignment((Stmt) caller, arg, cfg, visited);
									if(subrs != null){
										for(String t : subrs)
											rs.add(t);
									}
								}
							}
						}
					}
				}
			}
			else if(stmt instanceof InvokeStmt){
				InvokeStmt is = (InvokeStmt)stmt;
				InvokeExpr ie = is.getInvokeExpr();
				if(ie.getMethod().getName().equals("append") &&
						ie.getMethod().getDeclaringClass().getName().equals("java.lang.StringBuilder")){
					Value base = ((InstanceInvokeExpr)(ie)).getBase();
					if(base == target)
						findStringHelperHandleAppendMethod(ie, stmt, rs, cfg, visited);
				}
				else if(ie.getMethod().getName().equals("<init>")){
					try{
						InstanceInvokeExpr iie = (InstanceInvokeExpr)ie;
						Value base = iie.getBase();
						if(base == target){
							NUDisplay.debug("Dealing init method: "+stmt, null);
							for(int i=0; i<iie.getArgCount(); i++){
								if(iie.getMethod().getParameterType(i).toString().equals("java.lang.String")){
									NUDisplay.debug("  Dealing string arg: "+i, null);
									Value arg = iie.getArg(i);
									List<Unit> preds = cfg.getPredsOf(stmt);
									if(arg instanceof Constant){
										rs.add(arg.toString());
									}
									else{
										List<String> valStrs = null;
										for(Unit pred : preds){
											HashSet<Stmt> newVisited = new HashSet<Stmt>();
											newVisited.addAll(visited);
											valStrs = findLastResStringAssignment((Stmt)pred, arg, cfg, newVisited );
											if(valStrs!=null && valStrs.size()>0){
												rs.addAll(valStrs);
											}
										}
									}
								}
							}
						}
					}
					catch(Exception e){ }
				}
			}
	
			// Continue the search upwards
			List<Unit> preds = null;
			if(cfg.getMethodOf(stmt).hasActiveBody()){
				UnitGraph g = new ExceptionalUnitGraph(cfg.getMethodOf(stmt).getActiveBody());
				preds = g.getPredsOf(stmt);
			}
			else
				preds = cfg.getPredsOf(stmt);
			
			if(preds.size() >= 1 ){
				Unit pred = preds.get(0);
				if (!(pred instanceof Stmt))
					continue;
				if(visited.contains(pred))
					continue;
				queue.add((Stmt)pred);
			}
			for (int i=1; i<preds.size(); i++) {
				Unit pred = preds.get(i);
				if (!(pred instanceof Stmt))
					continue;
				if(visited.contains(pred))
					continue;
				
				List<String> subrs = findLastResStringAssignment((Stmt) pred, target, cfg, visited);
				if(subrs != null)
					for(String t : subrs)
						rs.add(t);
			}
		}
		return rs;
	}
	private static void findStringHelperHandleNonParamMethod(InvokeExpr ie, List<String> rs, BiDiInterproceduralCFG<Unit, SootMethod>  cfg,
			Set<Stmt> visited){
		UnitGraph g = new ExceptionalUnitGraph(ie.getMethod().getActiveBody());
		GraphTool.displayGraph(g, ie.getMethod());
		List<Unit> tails = g.getTails();
		//NUDisplay.debug("  Do inter-procedure analysis:"+ie.getMethod().getName()+" "+tails.size(), null);
		for(Unit t : tails){
			if(t instanceof ReturnStmt){
				if(visited.contains(t)) continue;
				ReturnStmt returnStmt = (ReturnStmt)t;
//				NUDisplay.debug("    start", "findLastResStringAssignment");
				List<String> subrs = findLastResStringAssignment((Stmt)t, returnStmt.getOp(), cfg, visited );
//				NUDisplay.debug("    ReturnVal:"+returnStmt.getOp()+ " resolve as:"+subrs.size()+" strings "+cfg, 
//						"findLastResStringAssignment");
				if(subrs != null) rs.addAll(subrs);
			}
		}
	}
	private static void findStringHelperHandleRegularMethod(InvokeExpr ie, Stmt stmt, List<String> rs, BiDiInterproceduralCFG<Unit, SootMethod>  cfg,
			Set<Stmt> visited){
		UnitGraph g = new ExceptionalUnitGraph(ie.getMethod().getActiveBody());
		GraphTool.displayGraph(g, ie.getMethod());
		List<Unit> tails = g.getTails();
//		NUDisplay.debug("  Do inter-procedure analysis:"+ie.getMethod().getName()+" "+tails.size(), null);
		for(Unit t : tails){
			if(t instanceof ReturnStmt){
				if(visited.contains(t)) continue;
				ReturnStmt returnStmt = (ReturnStmt)t;
				//NUDisplay.debug("    start", "findLastResStringAssignment");
				List<String> subrs = findLastResStringAssignment((Stmt)t, returnStmt.getOp(), cfg, visited );
//				NUDisplay.debug("    ReturnVal:"+returnStmt.getOp()+ " resolve as:"+subrs.size()+" strings "+cfg, 
//						"findLastResStringAssignment");
				if(subrs != null) rs.addAll(subrs);
			}
		}
		
		if(ie.getArgCount() == 0)
			return ;
		for(Value arg : ie.getArgs()){
			if(arg instanceof StringConstant){
				rs.add(((StringConstant) arg).value);
				continue;
			}
			else if(arg instanceof Constant)
				continue;
			
			for(Unit pred : cfg.getPredsOf(stmt)){
				HashSet<Stmt> newVisited = new HashSet<Stmt>();
				newVisited.addAll(visited);
				List<String> argStrs = findLastResStringAssignment((Stmt)pred, arg, cfg, newVisited );
				if(argStrs==null || argStrs.size()==0)
					continue;
				for(String argVal : argStrs)
					rs.add(argVal);
			}
		}
		
	}
	private static void findStringHelperHandleAppendMethod(InvokeExpr ie, Stmt stmt, List<String> rs, BiDiInterproceduralCFG<Unit, SootMethod>  cfg,
			Set<Stmt> visited){
		try{
			//handle base
			Value base = ((InstanceInvokeExpr)ie).getBase();
			List<String> baseStrs = null;
			List<Unit> preds = cfg.getPredsOf(stmt);
			for(Unit pred : preds){
				HashSet<Stmt> newVisited = new HashSet<Stmt>();
				newVisited.addAll(visited);
				baseStrs = findLastResStringAssignment((Stmt)pred, base, cfg, newVisited );
				//NUDisplay.debug("Found "+(baseStrs==null?"0":baseStrs.size())+" strs", null);
			}
			
			//handle arg.
			Value arg = ie.getArg(0);
			//NUDisplay.debug("  ## start handling arg:"+arg, null);
			if(arg instanceof Constant){
				//NUDisplay.debug("    ** append arg is a constant:"+arg, null);
				if(baseStrs==null || baseStrs.size()==0)
					rs.add(arg.toString());
				else{
					for(String baseStr : baseStrs)
						rs.add(baseStr+","+arg.toString());
				}
			}
			else{
				List<String> valStrs = null;
				for(Unit pred : preds){
					HashSet<Stmt> newVisited = new HashSet<Stmt>();
					newVisited.addAll(visited);
//					NUDisplay.debug("    ** append arg is NOT a constant:"+arg, null);
					valStrs = findLastResStringAssignment((Stmt)pred, arg, cfg, newVisited );
					if(valStrs==null || valStrs.size()==0){
						if(baseStrs!=null && baseStrs.size()>0)
							rs.addAll(baseStrs);
					}
					else{
						if(baseStrs==null || baseStrs.size()==0)
							rs.addAll(valStrs);
						else{
							for(String baseStr : baseStrs)
								for(String valStr : valStrs)
									rs.add(baseStr+","+valStr);
						}
					}
				}
				
			}
		}
		catch(Exception e){
			NUDisplay.alert("StringBuilder.append is not instance invoke expr:"+stmt, "findLastResStringAssignment");
		}
	}
	
	private static void findStringHelperHandleFormatMethod(InvokeExpr ie, Stmt stmt, List<String> rs, BiDiInterproceduralCFG<Unit, SootMethod>  cfg,
			Set<Stmt> visited){
		Value format = ie.getArg(0);
		List<String> bases = new ArrayList<String>();
		List<Unit> preds = cfg.getPredsOf(stmt);
		if(format instanceof StringConstant)
			rs.add(((StringConstant) format).value+" ");
		else{
			List<String> subvals = null;
			for(Unit pred : preds){
				HashSet<Stmt> newVisited = new HashSet<Stmt>();
				newVisited.addAll(visited);
				subvals = findLastResStringAssignment((Stmt)pred, format, cfg, newVisited );
				if(subvals != null){
					for(String v : subvals)
						rs.add(v);
				}
			}
		}
		
		NUDisplay.debug("  handling Sting.format's format:"+bases.size(), "findLastResStringAssignment");
		List<String> vals = new ArrayList<String>();
		for(int i=1; i<ie.getArgCount(); i++){
			Value val = ie.getArg(i);
			if(val instanceof StringConstant)
				vals.add(((StringConstant) val).value);
			else if(val instanceof Constant)
				vals.add(val.toString());
			else{
				List<String> subvals = null;
				for(Unit pred : preds){
					HashSet<Stmt> newVisited = new HashSet<Stmt>();
					newVisited.addAll(visited);
					subvals = findLastResStringAssignment((Stmt)pred, val, cfg, newVisited );
					if(subvals != null){
						for(String v : subvals)
							vals.add(v);
					}
				}	
			}
		}
		if(bases.size() > 0){
			if(vals.size() > 0)
				for(String base : bases)
					for(String val : vals)
						rs.add(base+","+val);
			else
				rs.addAll(bases);
		}
		else 
			rs.addAll(vals);
		
		NUDisplay.debug("  handling Sting.format's value:"+rs.size()+" strings", "findLastResStringAssignment");
	}
	
	private static Value findStringHelperHandleFieldRef(FieldRef fr, Stmt stmt, List<String> rs, BiDiInterproceduralCFG<Unit, SootMethod>  cfg,
			Set<Stmt> visitedStmts){
		
		SootField field = (fr).getField();
		boolean flag = false;
		for (Tag tag : field.getTags()){
			if (tag instanceof StringConstantValueTag){
				rs.add(((StringConstantValueTag) tag).getStringValue());
				flag = true;
			}
		}
		if(flag) return null;
		
		if(fr instanceof StaticFieldRef  || fr instanceof InstanceFieldRef){
			List<Stmt> fieldDefs = findFiledRef(fr);
			if(fieldDefs.size() == 0){
				rs.add("[NUTAG] <CLASSFIELD>"+fr.getField().getDeclaringClass().getName()+"."+fr.getField().getName());
				return null;
			}
			HashSet<Value> visited = new HashSet<Value>();
			Queue<Stmt> queue = new LinkedList<Stmt>();
			for(Stmt def : fieldDefs)
				queue.add(def);
//			NUDisplay.debug("In findStringHelperHandleFieldRef", null);
			while(!queue.isEmpty()){
				Stmt def = queue.poll();
				AssignStmt asDef = (AssignStmt)def;
				Value right = asDef.getRightOp();
				if(visited.contains(right)) continue;
				visited.add(right);
				NUDisplay.debug("  field ref defined at:" + def, "findLastResStringAssignment");
				
				if(right instanceof StringConstant)
					rs.add(((StringConstant) right).value);
				else if(right instanceof Constant)
					rs.add(right.toString());
				else if(right instanceof ArrayRef){
					return right;
				}
				else if(right instanceof FieldRef){
					NUDisplay.debug("    gotoField:"+right, null);
					fieldDefs = findFiledRef((FieldRef)right);
					for(Stmt d : fieldDefs)
						queue.add(d);
				}
				else{
//					Set<Stmt> visited2 = new HashSet<Stmt>();
//					visited2.add(stmt);
					NUDisplay.debug("    gotoSTMT:"+right+" "+def, null);
					List<String> ret = findLastResStringAssignment(def, right, cfg, visitedStmts);
					if(ret != null) 
						rs.addAll(ret);
				}
			}
			return null;
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
	
	public static void setCFGStartingTime(){
		cfgStartingTime = System.currentTimeMillis();
	}
	
	public static void findViewDefStmt(Stmt stmt, Value target, List<NUAccessPath> bases,
			BiDiInterproceduralCFG<Unit, SootMethod> cfg, Set<Stmt> visited, Set<Stmt> rs){
		long timeDiffSeconds = (System.currentTimeMillis() - cfgStartingTime)/1000;
		if(timeDiffSeconds > 300){//5mins
			//NUDisplay.error("passed time diff findViewDefStmt: "+timeDiffSeconds, null);
			return ;
		}
		
		if(visited.contains(stmt))
			return ;
		if(cfg == null){
			NUDisplay.error("Error: findViewDefStmt: cfg is not set", null);
			return ;
		}
		
		Stack<Stmt> stack = new Stack<Stmt>();
		stack.add(stmt);
		
		while(!stack.isEmpty()){
			timeDiffSeconds = (System.currentTimeMillis() - cfgStartingTime)/1000;
			if(timeDiffSeconds > 300){//5mins
				//NUDisplay.error("passed time diff findViewDefStmt2: "+timeDiffSeconds, null);
				return;
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
	private static List<Stmt> findFiledRef(FieldRef fr){
		List<Stmt> rs = new ArrayList<Stmt>();
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
		    		if(fr instanceof StaticFieldRef){
		    			StaticFieldRef sfr = (StaticFieldRef)fr;
		    			if(left instanceof StaticFieldRef){
		    				
		    				if(sfr.getField().getName().equals(((StaticFieldRef) left).getField().getName()) &&
		    						sfr.getField().getDeclaringClass().getName().equals(
		    								((StaticFieldRef) left).getField().getDeclaringClass().getName())){
		    					System.out.println("DEBUGField:"+fr+" "+s);
		    					rs.add(s);
		    				}
		    			}
		    		}
		    		else if(fr instanceof InstanceFieldRef){
		    			InstanceFieldRef ifr = (InstanceFieldRef)fr;
		    			if(left instanceof InstanceFieldRef){
		    				if(ifr.getField().getName().equals(((InstanceFieldRef) left).getField().getName()) &&
		    						ifr.getField().getDeclaringClass().getName().equals(
		    								((InstanceFieldRef) left).getField().getDeclaringClass().getName())){
		    					System.out.println("DEBUGField:"+fr+" "+s);
		    					rs.add(s);
		    				}
		    			}
		    		}
		    	}
		    }
		 }
		return rs;
	}
	
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
		    			set.add(ToolSet.createStmtSignatureWithMethod(s, ie.getMethod()));
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
		    		String sig = ToolSet.createStmtSignatureWithMethod(s, ie.getMethod());
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
