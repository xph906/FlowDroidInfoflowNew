package soot.jimple.infoflow.nu;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Base64;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.Base64.Decoder;

public class URLHostExtractor {
	final Pattern METHOD_CALL_PATTERN = Pattern.compile("\\<(.)+?\\>");
	final Pattern IP_PATTERN = Pattern.compile("(\\d){1,3}\\.(\\d){1,3}\\.(\\d){1,3}\\.(\\d){1,3}");
	final Set<String> tlds = new HashSet<String>();
	final Map<String, Integer> fieldCount = new HashMap<String, Integer>();
	final Map<String, Integer> methodCount = new HashMap<String, Integer>();
	final Pattern BASE64_PATTERN = Pattern.compile("^([A-Za-z0-9+/]{4})*([A-Za-z0-9+/]{4}|[A-Za-z0-9+/]{3}=|[A-Za-z0-9+/]{2}==)$");
	
	public static void main(String[] args) {
		URLHostExtractor m = new URLHostExtractor();
		m.installTLDs("../soot-infoflow-android/tlds.txt");
		m.readURLFile2("../urls.log");
		
		String a="abcde sdef,fnnn";
		String[] tmp = a.split("[ ,]");
		for(String t : tmp)
			System.out.println(t);
	}
	
	private Map<String, List<String> > readURLFile2(String filename){
		Map<String, List<String>> rs= new HashMap<String, List<String>>();
		BufferedReader br = null;
		FileReader fr = null;
		try {

			fr = new FileReader(filename);
			br = new BufferedReader(fr);

			String line;
			int cnt = 0;
			int bad = 0;
			br = new BufferedReader(new FileReader(filename));
			while ((line = br.readLine()) != null) {
				
				Set<String> vals = processURL(line.trim());
				if(vals.size() > 0)
					for(String val : vals)
						System.out.println("HOST:"+val);
				
			}
			System.out.println("Count: "+cnt+" vs "+bad);
			

		} catch (IOException e) {

			e.printStackTrace();

		} 	
		for(String key : fieldCount.keySet()){
			System.out.println("FC:"+key+" : "+fieldCount.get(key));
		}
		for(String key : methodCount.keySet()){
			System.out.println("MC:"+key+" : "+methodCount.get(key));
		}
		return rs;
	}
	
	private Map<String, List<String> > readURLFile(String filename){
		Map<String, List<String>> rs= new HashMap<String, List<String>>();
		BufferedReader br = null;
		FileReader fr = null;
		try {

			fr = new FileReader(filename);
			br = new BufferedReader(fr);

			String line;
			int cnt = 0;
			int bad = 0;
			br = new BufferedReader(new FileReader(filename));
			while ((line = br.readLine()) != null) {
				String[] tmp = line.split(":");
				
				if(tmp==null || tmp.length<3) continue;
				String fname = tmp[0].trim();	
				Set<String> vals = null;
				String target = null;
				if(tmp.length > 3){
					StringBuilder sb = new StringBuilder();
					for(int i=2; i<tmp.length; i++)
						sb.append(tmp[i]);
					target = sb.toString();
					vals = processURL(target);
				}
				else{
					target = tmp[2];
					vals = processURL(tmp[2]);
				}
				if(vals.size() > 0){
					cnt++;
					System.out.println(fname);
					for(String v : vals)
						System.out.println("  "+v);
				}
				else {
					bad++;
					//System.out.println(target);
				}
			}
			System.out.println("Count: "+cnt+" vs "+bad);
			

		} catch (IOException e) {

			e.printStackTrace();

		} 	
		for(String key : fieldCount.keySet()){
			System.out.println("FC:"+key+" : "+fieldCount.get(key));
		}
		for(String key : methodCount.keySet()){
			System.out.println("MC:"+key+" : "+methodCount.get(key));
		}
		return rs;
	}
	
	public Set<String> processURL(String line){
		Set<String> rs = new HashSet<String>();
		try{
			String[] elems = line.split(",");
			if(elems==null || elems.length==0){
				return rs;
			}
			for(String elem : elems){
				String[] cells = elem.split(" ");
				for(String cell : cells){
					cell = cell.trim().toLowerCase();
					if(cell.length()==0) continue;
					String host = cell;
					int idx = cell.indexOf("//");
					if(idx != -1){ 
						idx += 2;
						host = cell.substring(idx);
					}
	//				
					int idx2 = host.indexOf(":");
					idx = host.indexOf("/");
					
					if(idx!=-1 && idx2!=-1)
						host = host.substring(0, Math.min(idx, idx2));
					else if(idx==-1 && idx2==-1)
						host = host.trim();
					else
						host = host.substring(0, Math.max(idx, idx2));
	//				System.out.println("DEBUG:"+host+" "+idx+"/"+idx2);
					String[] es = host.split("\\.");
					if(es.length <= 1) continue;
	//				System.out.println("DEBUG:"+host);
					if(tlds.contains(es[es.length-1].trim())){
						String tmp = es[es.length-2].trim()+"."+es[es.length-1].trim();
						if(tlds.contains(tmp)){
							if(es.length>2)
								rs.add(es[es.length-3]+"."+tmp);
						}
						else
							rs.add(tmp);
					}
					else {
						Matcher mat = IP_PATTERN.matcher(host);
						if(mat.find())
							rs.add(host);
					}
				}
			}
		
			if(rs.size() == 0){
				for(String elem : elems){
					String[] tmp = elem.split(" ");
					for(String t : tmp){
						Matcher m = BASE64_PATTERN.matcher(t);
						if(m.find()){
							String x = new String(Base64.getDecoder().decode(t)).toLowerCase();
							if(x.startsWith("http")){
//								rs.add(x);
								String cell = x;
								String host = x;
								int idx = cell.indexOf("//");
								if(idx != -1){ 
									idx += 2;
									host = cell.substring(idx);
								}
				//				
								int idx2 = host.indexOf(":");
								idx = host.indexOf("/");
								
								if(idx!=-1 && idx2!=-1)
									host = host.substring(0, Math.min(idx, idx2));
								else if(idx==-1 && idx2==-1)
									host = host.trim();
								else
									host = host.substring(0, Math.max(idx, idx2));
								String[] es = host.split("\\.");
								if(es.length <= 1) continue;
								if(tlds.contains(es[es.length-1].trim())){
									String tmp3 = es[es.length-2].trim()+"."+es[es.length-1].trim();
									if(tlds.contains(tmp3)){
										if(es.length>2)
											rs.add(es[es.length-3]+"."+tmp3);
									}
									else
										rs.add(tmp3);
								}
								else {
									Matcher mat = IP_PATTERN.matcher(host);
									if(mat.find())
										rs.add(host);
								}
							}
						}
					}
				}
			}
		}
		catch(Exception e){}
		//System.out.println("found "+rs.size()+" urls");
		return rs;
	}
	
	public void installTLDs(String filename){
		BufferedReader br = null;
		FileReader fr = null;
		try {
			fr = new FileReader(filename);
			br = new BufferedReader(fr);
			String line;
			br = new BufferedReader(new FileReader(filename));
			while ((line = br.readLine()) != null) {
				if(line.startsWith("//")) continue;
				line = line.trim();
				tlds.add(line);
			}

		} catch (IOException e) {
			e.printStackTrace();
		} 	
		System.out.println("has read "+tlds.size()+" tlds.");
	}
	
	private <K,V> void addToMapList(Map<K,List<V>> map, K key, V val) {
		if(map.containsKey(key))
			map.get(key).add(val);
		else{
			List<V> vals = new ArrayList<V>();
			vals.add(val);
			map.put(key, vals);
		}
	}
	private <K> void incrementKeyVal(Map<K,Integer> map, K key) {
		int val = 1;
		if(map.containsKey(key))
			val = ((Integer)map.get(key)) + 1 ;
	
		map.put(key, val);
		
	}
	
	
}
