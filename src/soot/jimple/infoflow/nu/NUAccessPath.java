package soot.jimple.infoflow.nu;

import java.util.ArrayList;
import java.util.List;

import soot.Local;
import soot.SootField;
import soot.Value;
import soot.jimple.ArrayRef;
import soot.jimple.CastExpr;
import soot.jimple.Constant;
import soot.jimple.Expr;
import soot.jimple.InstanceFieldRef;
import soot.jimple.StaticFieldRef;

public class NUAccessPath {
	static public boolean containsAccessPath(List<NUAccessPath> lst, Value target){
		return findAccessPath(lst, target) != null;
	}
	static public NUAccessPath findAccessPath(List<NUAccessPath> lst, Value target){
		for(NUAccessPath ap : lst)
			if(ap.isSameValue(target))
				return ap;
		return null;
	}
	static public void addUniqueAccessPath(List<NUAccessPath> lst, Value target){
		//remove duplicates.
		NUAccessPath ap = findAccessPath(lst, target);
		if(ap == null)
			lst.add(new NUAccessPath(target));
	}
	static public boolean containsAccessPathWithPrefix(List<NUAccessPath> lst, Value target){
		List<NUAccessPath> paths = findAccessPathWithPrefix(lst, target);
		if(paths!=null && paths.size()>0)
			return true;
		return false;
	}
	static public List<NUAccessPath> findAccessPathWithPrefix(List<NUAccessPath> lst, Value target){
		List<NUAccessPath> rs = new ArrayList<NUAccessPath>();
		for(NUAccessPath ap : lst)
			if(ap.isPrefix(target))
				rs.add(ap);
		return rs;
	}
	static public String listAPToString(List<NUAccessPath> lst){
		StringBuilder sb = new StringBuilder();
		for(NUAccessPath nap : lst)
			sb.append(nap+" ===  ");
		return sb.toString();
	}
	
	//Start NUAccessPath
	private List<Object> path = new ArrayList<Object>();
	
	public List<Object> getPath(){
		return path;
	}
	public boolean isSameValue(Value v){
		List<Object> tmp = new ArrayList<Object>();
		addValueToPath(v, tmp);
		if(tmp.size() != path.size())
			return false;
		for(int i=0; i<path.size(); i++)
			if(!resolvePathValue(path.get(i)).equals(resolvePathValue(tmp.get(i))))
				return false;
		return true;
	}
	public boolean isPrefix(Value v){
		List<Object> tmp = new ArrayList<Object>();
		addValueToPath(v, tmp);
		if(tmp.size() > path.size())
			return false;
		for(int i=0; i<tmp.size(); i++)
			if(!resolvePathValue(path.get(i)).equals(resolvePathValue(tmp.get(i))))
				return false;
		return true;
	}
	
	@Override
	public boolean equals(Object o){
		if(!(o instanceof NUAccessPath))
			return false;
		NUAccessPath other = (NUAccessPath)o;
		List<Object> lst = other.getPath();
		if(lst.size() != path.size())
			return false;
		for(int i=0; i<path.size(); i++)
			if(!resolvePathValue(path.get(i)).equals(resolvePathValue(lst.get(i))))
				return false;
		return true;
	}
	
	public void replacePrefix(Value oldValue, Value newValue){
		List<Object> oldPath = new ArrayList<Object>();
		addValueToPath(oldValue, oldPath);
		List<Object> newPath = new ArrayList<Object>();
		addValueToPath(newValue, newPath);
		for(int i=oldPath.size(); i<path.size(); i++)
			newPath.add(path.get(i));
		path = newPath;
	}
	
	//Constructor
	public NUAccessPath(NUAccessPath other){
		for(Object obj : other.getPath())
			path.add(obj);
	}
	
	public NUAccessPath(Value v){
		addValueToPath(v, path);
	}
	
	private void addValueToPath(Value v, List<Object> curpath){
		if(v instanceof Local || v instanceof StaticFieldRef)
			curpath.add(v);
		else if(v instanceof ArrayRef){
			//TODO: what to do with array?
			curpath.add(v);
		}
		else if(v instanceof InstanceFieldRef){
			addValueToPath(((InstanceFieldRef) v).getBase(), curpath);
			curpath.add(((InstanceFieldRef) v).getField());
		}
		else if(v instanceof CastExpr){
			CastExpr ce = (CastExpr)v;
			addValueToPath(ce.getOp(),curpath);
		}
		else if(v instanceof Expr){
		//	System.out.println("addValueToPath type error(expr): "+v);
		}
		else{
		//	System.out.println("addValueToPath type error(unknown): "+v);
		}
	}
	
	public String resolvePathValue(Object v){
		if(v instanceof Local)
			return ((Local)v).getName();
		else if(v instanceof ArrayRef){
			ArrayRef ar = (ArrayRef)v;
			return resolvePathValue(ar.getBase())+"["+resolvePathValue(ar.getIndex())+"]";
		}
		else if(v instanceof StaticFieldRef){
			StaticFieldRef sfr = (StaticFieldRef)v;
			return sfr.getField().getDeclaringClass().getName()+"."+sfr.getField().getName();
		}
		else if(v instanceof Constant)
			return ((Constant)v).toString();
		else if(v instanceof SootField)
			return ((SootField)v).getName();
		else
			return v.toString();
	}
	
	public String toString(){
		StringBuilder sb = new StringBuilder();
		for(Object v : path){
			if(sb.length() > 0)
				sb.append(".");
			sb.append(resolvePathValue(v));
		}
		return sb.toString();
	}
}
