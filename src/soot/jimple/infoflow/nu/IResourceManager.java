package soot.jimple.infoflow.nu;

public interface IResourceManager {
	public String getTextsById(int id);
	public String getStringById(int id);
	public Integer getResourceIdByName(String name);
	public int resourcePakcageSize();
	public Integer getResourceId(String resName, String resID, String packageName);
	
}
