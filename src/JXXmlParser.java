import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.Arrays;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;
import org.xml.sax.SAXException;

/***
 * @author xincafe
 * @description this class is used for parsing XML-based documents
 * @date 8/15/2016
 */
public class JXXmlParser {

	String inputDir = "input\\JXXmlParser";
	String workingDir = System.getProperty("user.dir") + "\\" + inputDir; 
	String basefile = "base";
	String resultfile = "result";
	
	public JXXmlParser() {
		
	}
	
	public void run() {
		//System.out.println("workingDir = " + workingDir);
		File workingdir = new File(workingDir);
		//System.out.println("workingdir = " + workingdir);
		for (File dir: workingdir.listFiles()) {
			//System.out.println("dir = " + dir);
			File base;
			File result;
			//System.out.println("dir.listFiles = *" + dir.listFiles()[0] + "*");
			if (dir.listFiles()[0].toString().indexOf( basefile ) >= 0) {
				base = dir.listFiles()[0];
				result = dir.listFiles()[1];	
			} else {
				base = dir.listFiles()[1];
				result = dir.listFiles()[0];
			}
			System.out.println("base = " + base.toString());
			System.out.println("result = " + result.toString());
			computeForEachPair(dir.toString(), base, result);
		}
	}
	
	public void computeForEachPair(String dir, File base, File result) {
		Document xml = null;
		try {
			DocumentBuilderFactory dbf = DocumentBuilderFactory.newInstance();
			DocumentBuilder db = dbf.newDocumentBuilder();
			xml = db.parse(base);
			xml.getDocumentElement().normalize();
		} catch (ParserConfigurationException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (SAXException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		NodeList nodelist = xml.getElementsByTagName("OPINFO");
		

		//for placing results
		String[] totalstr = new String[200];
		int len_totalstr = 0;
		
		try {
			BufferedReader bfreader = new BufferedReader(new FileReader(result));
			String tmpstr;
			while ((tmpstr=bfreader.readLine()) != null) {
				bfreader.readLine();
				int a = Integer.parseInt( tmpstr.split(" ")[0] );
				int b = Integer.parseInt( tmpstr.split(" ")[1] );
				if (a >= b)
					System.err.println("ERROR - a >= b");
				//System.out.println("a & b = " + a + " & " + b);
				Node node_a = nodelist.item( a );
				Node node_b = nodelist.item( b );
				if (node_a.getNodeType() != Node.ELEMENT_NODE)
					System.err.println("ERROR - node_a.getNodeType() != Node.ELEMENT_NODE !!");
				Element ele_a = (Element) node_a;
				Element ele_b = (Element) node_b;
				if (Integer.parseInt(ele_a.getAttribute("ID")) != a)
					System.err.println("ERROR - != a");
				if (Integer.parseInt(ele_b.getAttribute("ID")) != b)
					System.err.println("ERROR - != b");
				//System.out.println("Fine");
				
				Element stacks_a = (Element) ((Element)ele_a.getElementsByTagName("Operation").item(0)).getElementsByTagName("Stacks").item(0);
				Element stacks_b = (Element) ((Element)ele_b.getElementsByTagName("Operation").item(0)).getElementsByTagName("Stacks").item(0);
				int len_a = Integer.parseInt( stacks_a.getAttribute("Len") );
				int len_b = Integer.parseInt( stacks_b.getAttribute("Len") );
				//System.out.println("ID & Len = " + a + ":" + len_a + " " + b + ":" + len_b);
				
				String sstr_a = "";
				String sstr_b = "";
				for (int i = 0; i < len_a; i++) {
		            Element ele = (Element) stacks_a.getElementsByTagName("Stack").item(i);
		            String xclass = ele.getElementsByTagName("Class").item(0).getTextContent();
			        String xmethod= ele.getElementsByTagName("Method").item(0).getTextContent(); 
			        String xline  = ele.getElementsByTagName("Line").item(0).getTextContent();
			        sstr_a = sstr_a + xclass + xmethod + xline;
		  	   }
			   for (int i = 0; i < len_b; i++) {
		            Element ele = (Element) stacks_b.getElementsByTagName("Stack").item(i);
		            String xclass = ele.getElementsByTagName("Class").item(0).getTextContent();
			        String xmethod= ele.getElementsByTagName("Method").item(0).getTextContent(); 
			        String xline  = ele.getElementsByTagName("Line").item(0).getTextContent();
			        sstr_b = sstr_b + xclass + xmethod + xline;
		  	   }
			   
			   if (sstr_a.compareTo(sstr_b) != 0)
				   System.err.println("WARN - sstr_a.compareTo(sstr_b) != 0");
			   
			   String sstr_ab = "";
			   //sstr_ab = sstr_a + sstr_b;
			   if (sstr_a.compareTo(sstr_b) <= 0)
				   sstr_ab = sstr_a + sstr_b;
			   else 
				   sstr_ab = sstr_b + sstr_a;
			   //System.out.println("sstr_ab = " + sstr_ab);
			   totalstr[len_totalstr++] = sstr_ab;
			}
			
			//Get results
			System.out.println("Results for " + dir + "-\n" + "len_totalstr = " + len_totalstr);
			Arrays.sort(totalstr, 0, len_totalstr);
			int groups = 1;
			for (int i=1; i<len_totalstr; i++) {
				System.out.print( totalstr[i] );
				if (totalstr[i].compareTo( totalstr[i-1] ) != 0) {
					groups ++;
					System.out.println("-------------------\n");
				}
				else {
					System.out.println();
				}
			}
			System.out.println("Groups = " + groups);
			System.out.println();
		} catch (FileNotFoundException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}	
        
	}
	
	public static void main(String[] args) {
		// TODO Auto-generated method stub
		JXXmlParser parser = new JXXmlParser();
		parser.run();
	}

}
