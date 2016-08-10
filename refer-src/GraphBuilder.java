/**
 * Created by guangpu on 3/21/16.
 */
package com.da;
import java.io.*;
import java.io.InterruptedIOException;
import java.io.PrintWriter;

import java.util.*;
import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.transform.OutputKeys;
import javax.xml.transform.Transformer;
import javax.xml.transform.TransformerFactory;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;


import org.w3c.dom.*;
import com.da.Pair;
import org.w3c.dom.Document;
import org.w3c.dom.Element;


public class GraphBuilder {

    class IdPair implements Comparable<IdPair>{
        int pid;
        int tid;
        public IdPair(int p, int t) {
            this.pid = p;
            this.tid = t;
        }
        public String toString(){
            return "["+pid+","+tid+"]";
        }
        public int compareTo(IdPair idPair){
            Integer Tid = this.tid;
            return Tid.compareTo(idPair.tid);
        }

    }

    class EgPair {
        int source;
        int destination;
        public EgPair( int f, int t){
            source = f;
            destination = t;
        }
    }

    String xmldir;                                    // the directory containing log files to process
    Document inputdoc;				      // xml input variable	
    Document outputdoc ;			      // xml output file
    Element  docroot;

    ArrayList<Node> nList;                            //node list of all the file
    ArrayList<ArrayList<Pair>> edge;                  //adjcent list of edges of the happen before graph
    ArrayList<ArrayList<Pair>> backedge;              //adjcent list of backward edges for tracing back
    ArrayList<HashSet<Integer>> reach;                //reach[i] = set of reachable node form Node I
    HashMap <String, ArrayList<Integer> >memref;      //memref[madd] = set of nodes which read or write memory location madd
    ArrayList<IdPair> idplist;                        //idplist[i] includes the pid and tid of node i
    HashMap <IdPair, ArrayList<Integer>> ptidref;     //ptidref(idpair) includes the node in ptid from the beginning to end
    HashMap <String, ArrayList<Integer>> typeref;     //add the same optype to a same list

    HashMap <String, ArrayList<Integer>> hashMsgSending;     //hashMsg(key) is a list of nodes whose OPVAL is the key and type is msgsending
    HashMap <String, ArrayList<Integer>> hashMsgProcEnter;   //hashNsgProcEnter(key) is a list of nodes whose OPVAL is the key and type is msgProcEnter

    HashMap <IdPair, ArrayList<Integer>> ptidsyncref; //ptidsyncref(idpair, i) means ith sync node in idpair thread
    //sync node includes MsgSending MsgProcEnter EventProcEnter ThdCreate ThdEnter
    //
    ArrayList<HashMap <IdPair, Integer>> vectorclock; // vectorclock of one node is a hashmap <ptid,int>... 
    ArrayList<ArrayList<EgPair>> syncedges;           // sync edges set, rpc call event handle...

    ArrayList<BitSet> reachbitset;                    // 
    ArrayList<Integer> eventend;                      // i is a event start and eventend[i] is its end
    ArrayList<Integer> eventcaller;		      // i is a event start and eventcaller[i] is its caller	
    HashMap <IdPair, ArrayList<Integer>> ptideventref; //
    ArrayList<Integer> emlink;                         // event msg back tracking
    ArrayList<Integer> emlink2;                        // event msg back tracking verstion 2
    int [] flag;
    ArrayList<Integer> root;                          // unheaded threads 
    int esum;
    HashMap <IdPair, Integer> outputlist; 		//for simple output
    HashMap <IdPair, Integer> outputlist2;		//for median output
    HashMap <String, Integer> identity;			//group the same operation

    ArrayList<Integer> msender; 		//where is the message sender
    ArrayList<Integer> mexit;			//where is the message exit
    ArrayList<Integer> eexit;			//where is the event exit
					//where is the event enqueue [eventcaller]
    
    ArrayList<Integer> zkcreatelist;
    int getcurdotrans = 0;
    int twodotrans = 0;
    int unigetstate = 0;
    int unitwotrans = 0;
    int uni3=0;
    int uni4=0;
    boolean mr = false;
    boolean hb = false;	
    boolean samethread(int x, int y){
	IdPair ipx = idplist.get(x);
	IdPair ipy = idplist.get(y);
	if (ipx.pid != ipy.pid) return false;
	if (ipx.tid != ipy.tid) return false;
	return true;
    }
    public GraphBuilder(String xmldirctory) {
        xmldir = xmldirctory;
 //       System.out.println(xmldir);
	if (xmldir.contains("MR") || xmldir.contains("mr")) mr = true;
	if (xmldir.contains("HB") || xmldir.contains("hb")) hb = true;
        esum = 0;
        nList = new ArrayList<Node>();
        edge  = new ArrayList<ArrayList<Pair>>();
        backedge  = new ArrayList<ArrayList<Pair>>();
        root = new ArrayList<Integer>();
        idplist = new ArrayList<IdPair>();
        ptidref = new HashMap<IdPair,ArrayList<Integer>>();
        ptideventref = new HashMap<IdPair,ArrayList<Integer>>();
        typeref = new HashMap<String,ArrayList<Integer>>();
        memref = new HashMap<String , ArrayList<Integer>>(nList.size());
        hashMsgSending = new HashMap<String, ArrayList<Integer>>();
        hashMsgProcEnter = new HashMap<String, ArrayList<Integer>>();
        syncedges = new ArrayList<ArrayList<EgPair>>(50);
        /*
        syncedges.add(new ArrayList<EgPair>());
        syncedges.add(new ArrayList<EgPair>());
        syncedges.add(new ArrayList<EgPair>());
        syncedges.add(new ArrayList<EgPair>());
 	syncedges.set(10, new ArrayList<EgPair>());
 	syncedges.set(20, new ArrayList<EgPair>());
 	syncedges.set(30, new ArrayList<EgPair>());
        */
        outputlist  = new HashMap<IdPair, Integer>();
        outputlist2 = new HashMap<IdPair, Integer>();
        identity = new HashMap<String, Integer>();
	emlink   = new ArrayList<Integer>();
	emlink2  = new ArrayList<Integer>();
    File [] xmlfiles = new File(xmldirctory).listFiles();
	msender = new ArrayList<Integer>();
	mexit = new ArrayList<Integer>();
	eexit = new ArrayList<Integer>();
	zkcreatelist = new ArrayList<Integer>();
        int index = 0;
        IdPair idPair;
        if (xmlfiles != null)
            for (File xml : xmlfiles) {
		Stack<Integer> stack = new Stack<Integer>();
                String xmlfilename = xml.getName();
                //System.out.println(xmlfilename);
                String [] ptid = xmlfilename.split("-");
                idPair = new IdPair(Integer.parseInt(ptid[0]), Integer.parseInt(ptid[1]));
                ArrayList<Integer> idlist = new ArrayList<Integer>();
                ArrayList<Integer> ideventlist = new ArrayList<Integer>();
                //System.out.println(ptid[0] + " ~ " + ptid[1]);
                //File xml = new File(xmlfile);
                //System.out.println(xml.toString());
                try {
                    DocumentBuilderFactory dbf = DocumentBuilderFactory.newInstance();
                    DocumentBuilder db = dbf.newDocumentBuilder();
                    inputdoc = db.parse(xml);
                    //System.out.println(document);
                } catch (Exception e) {
                    System.out.println("XML file load error, graphbuilder construction failed");
                    e.printStackTrace();
                }

                inputdoc.getDocumentElement().normalize();
                //System.out.println("Root element :" + document.getDocumentElement().getNodeName());

                NodeList NList = inputdoc.getElementsByTagName("Operation");
                int mheader = -1;
		int mflag   = 1;
		int curmsg = -1;
                for (int i = 0; i < NList.getLength(); i++) {
                    Node nNode = NList.item(i);
                    //System.out.println("\nCurrent Element :" + nNode.getNodeName());
	//	    System.out.println(ptid[0]+"-"+ptid[1]+" mheader = "+mheader+ " mflag = "+ mflag);
		    if ( goodnode(nNode) == false) continue;
		    if (nNode.getNodeType() == Node.ELEMENT_NODE) {
                        //System.out.println("++++ index=" + index + " "+ nNode);
                        Element eElement = (Element) nNode;
			String tp = eElement.getElementsByTagName("OPTY").item(0).getTextContent();
                        String tval = eElement.getElementsByTagName("OPVAL").item(0).getTextContent();
			
			if (i > 0){
			    Node pn = nList.get(index-1);
			    Element pe = (Element) pn;
			    String ptp = pe.getElementsByTagName("OPTY").item(0).getTextContent();
                            String pval = pe.getElementsByTagName("OPVAL").item(0).getTextContent();        
			    if (ptp.equals(tp) && pval.equals(tval)) continue;
			    /*if (i > 2){
				 
                        //	System.out.println("++++ i =" + i + " i>2");
	      		        pn = nList.get(index-2);
                                pe = (Element) pn;
                                ptp = pe.getElementsByTagName("OPTY").item(0).getTextContent();
                                pval = pe.getElementsByTagName("OPVAL").item(0).getTextContent();
                                if (ptp.equals(tp) && pval.equals(tval)) continue;
			    }*/
			}
                        //System.out.println("++++ index=" + index + " "+ nNode);
                        nList.add(nNode);
			String idstr = getIdentity(nNode);
			if (identity.keySet().contains(idstr)){
			    int freq = identity.get(idstr);
			    identity.put(idstr,freq+1);
			}else
			    identity.put(idstr,1);
			emlink.add(-1);
			mexit.add(-1);
			eexit.add(-1);
			msender.add(-1);
			if (stack.empty()){
			    emlink2.add(-1);
			} else{
			    emlink2.add(stack.peek());
			}
                        idplist.add(idPair);
                        edge.add(new ArrayList<Pair>());
                        backedge.add(new ArrayList<Pair>());
                        if ((i > 0)
			    &&(!tp.equals("ThdEnter"))
			    &&(!tp.equals("MsgProcEnter"))
			    &&(!tp.equals("EventProcEnter"))
			){
                            addedge(index-1,index);
			    if (mflag > 0) {
				mheader = index;
	//		        System.out.println("set mheader = "+index);
			    }
                        }
			if (tp.equals("MsgProcEnter")){
			    mflag = -1;
			    if (curmsg >-1)
				mexit.set(curmsg,index-1);
			    System.out.println("Form "+curmsg + " to "+ index+"-1 is a msg");
			    curmsg = index;
	//		    System.out.println("set mflag = -1");
			    if (mheader > -1) {
				addedge(mheader,index);
				System.out.println(index+ "is pluged to "+ mheader);
			    }else {
//				System.out.println(index+ "is a no program header msg from "+ptid[0]+"-"+ptid[1]);
			    }
			}
                        if (typeref.get(tp) == null)
                            typeref.put(tp,new ArrayList<Integer>());
                        typeref.get(tp).add(index);
                        idlist.add(index);
                        if (tp.equals("EventProcEnter")){
			    //stack.push(index);
                            String val = eElement.getElementsByTagName("OPVAL").item(0).getTextContent();
                            if (!val.contains("GenericEventHandler")){
                                ideventlist.add(index);
			        stack.push(index);
			    }
			    else addedge(index-1,index);
                        }
			if (tp.equals("EventProcExit")){
			    String val = eElement.getElementsByTagName("OPVAL").item(0).getTextContent();
			    if (!val.contains("GenericEventHandler"))
			    stack.pop();
			}
			if (tp.equals("HeapWrite")){
   			    Element esx = (Element) eElement.getElementsByTagName("Stacks").item(0);
			    Element sx = (Element) esx.getElementsByTagName("Stack").item(0);
			    String xmethod = sx.getElementsByTagName("Method").item(0).getTextContent();
			    if (xmethod.equals("createNonSequential"))
				zkcreatelist.add(index);
			}
                        
                        /*if (index == 18686) {
                            System.out.println("18686 eventput = "+ stack.peek());

                           //System.out.println("pid = " + idPair.pid +" tid = " +idPair.tid);
                        }*/
                        index ++;

//               System.out.println("Author : " + eElement.getElementsByTagName("author").item(0).getTextContent());

                    }
		    if (curmsg > -1) mexit.set(curmsg,index-1);
                }
                ptidref.put(idPair,idlist);
                ptideventref.put(idPair,ideventlist);
		if (typeref.get("MsgSending") == null)
                    typeref.put("MsgSending",new ArrayList<Integer>());
                if (typeref.get("MsgProcEnter") == null)
                    typeref.put("MsgProcEnter",new ArrayList<Integer>());
                if (typeref.get("ThdCreate") == null)
                    typeref.put("ThdCreate",new ArrayList<Integer>());
                if (typeref.get("ThdEnter") == null)
                    typeref.put("ThdEnter",new ArrayList<Integer>());
                if (typeref.get("ThdJoin") == null)
                    typeref.put("ThdJoin",new ArrayList<Integer>());
                if (typeref.get("ThdExit") == null)
                    typeref.put("ThdExit",new ArrayList<Integer>());
                if (typeref.get("MsgProcExit") == null)
                    typeref.put("MsgProcExit",new ArrayList<Integer>());
                if (typeref.get("EventProcEnter") == null)
                    typeref.put("EventProcEnter",new ArrayList<Integer>());
                if (typeref.get("EventProcExit") == null)
                    typeref.put("EventProcExit",new ArrayList<Integer>());
		if (typeref.get("ProcessCreate") == null)	
                    typeref.put("ProcessCreate",new ArrayList<Integer>());
		if (typeref.get("EventCreate") == null)	
                    typeref.put("EventCreate",new ArrayList<Integer>());
                /*if ((idPair.pid == 31943) &&(idPair.tid == 49)) {
                    System.out.println("####"+ ptidref.get(new IdPair(31943,49)));
                    gSendingystem.out.println("####"+ ptidref.get(idPair));
                }*/
		
            }
	    System.out.println(esum+"initialized edges are added.");
	    System.out.print("zkcreate = ");
	    System.out.println(zkcreatelist);
            createbasexml();
	    createemlink();

    }
    public String getIdentity(Node node){
	Element ex = (Element) node;
        String optyx = ex.getElementsByTagName("OPTY").item(0).getTextContent();
        Element esx = (Element) ex.getElementsByTagName("Stacks").item(0);
        String slenx = esx.getAttribute("Len");
	String id = optyx;
	for (int i = 0 ; i < Integer.parseInt(slenx); i++ ){
            Element sx = (Element) esx.getElementsByTagName("Stack").item(i);
            String xclass = sx.getElementsByTagName("Class").item(0).getTextContent();
	    String xmethod= sx.getElementsByTagName("Method").item(0).getTextContent(); 
	    String xline  = sx.getElementsByTagName("Line").item(0).getTextContent();
	    id = id + xclass + xmethod + xline;
  	}
	return id;
    }
    public boolean goodnode(Node node){
        Element ex = (Element) node;
        String optyx = ex.getElementsByTagName("OPTY").item(0).getTextContent();
        Element esx = (Element) ex.getElementsByTagName("Stacks").item(0);
        String slenx = esx.getAttribute("Len");
//	if (! optyx.equals("MsgProcEnter")) return true;
        String opvx = ex.getElementsByTagName("OPVAL").item(0).getTextContent();
//	if (opvx.contains("NodeChildrenChanged")) return false;
        for (int i = 0 ; i < Integer.parseInt(slenx); i++ ){
        //for (int i = 0 ; i < 1; i++ ){
            Element sx = (Element) esx.getElementsByTagName("Stack").item(i);
            String xclass = sx.getElementsByTagName("Class").item(0).getTextContent();
	    //if (xclass.contains("FileSnap")) return false;
	    /*
	    if (i == 0){
		String xlinum = sx.getElementsByTagName("Line").item(0).getTextContent();        if (optyx.equals("HeapRead") && xlinum.equals("-1")) return false;
		String xmethod = sx.getElementsByTagName("Method").item(0).getTextContent();     
		if (optyx.equals("HeapRead") && xmethod.equals("getCurrentState")) {
		Element s2 = (Element) esx.getElementsByTagName("Stack").item(1);
		String string = s2.getElementsByTagName("Line").item(0).getTextContent();
		if (string.equals("-1")) return false;
		}
	    } */ 
	    if (xclass.contains("FileTxnLog") && optyx.equals("MsgProcEnter")) return false;	
	    if (xclass.contains("FileSnap") && optyx.equals("MsgProcEnter")) return false;	
	    if (xclass.contains("FileTxnSnapLog") && optyx.equals("MsgProcEnter")) return false;	

        }

        return true;

    }
    public void createemlink(){
//	emlink = new ArrayList<Integer>(nList.size());
	for ( int i = 0 ; i < nList.size(); i++){
	    if (backedge.get(i).size() == 0) {
		Stack<Integer> stack = new Stack<Integer>();
		stack.push(-1);
		int cur = -1;
		int j = i;
//		emlink.set(j,-1);
		while (!edge.get(j).isEmpty()){
		    if (emlink.get(j) == -1){
    	                emlink.set(j,stack.peek());
			}

		        Node node = nList.get(j);
                        Element e = (Element) node;
			String opval= e.getElementsByTagName("OPVAL").item(0).getTextContent();
		        String opty = e.getElementsByTagName("OPTY").item(0).getTextContent();
		        if (opty.equals("ThdEnter")|| opty.equals("MsgProcEnter") || opty.equals("EventProcEnter")){
			    stack.push(j);
		        }
			//only works well for hadoop
		    	if ((opty.equals("ThdExit")||opty.equals("MsgProcExit")||opty.equals("EventProcExit")) && (stack.peek() != -1)){
			    Node nodex = nList.get(stack.peek());
			    Element ex = (Element) nodex;
			    if (ex.getElementsByTagName("OPVAL").item(0).getTextContent().equals(opval)){
			        int xx=stack.pop();
				if (opty.equals("EventProcExit")){
				    eexit.set(xx,j);
				}
			    }
			     
			} 
			if (opty.equals("EventProcExit") && (stack.peek() != -1)){
			    Node nodex = nList.get(stack.peek());
                            Element ex = (Element) nodex;
                            String st1=ex.getElementsByTagName("OPVAL").item(0).getTextContent();
			    String st2 = st1.split("!")[0];
			    String st3 = opval.split("!")[0];
			    if (st2.equals(st3)){
                                int xx = stack.pop();
				eexit.set(xx,j);
			    }
			}

		    	
		    j = edge.get(j).get(0).destination;
		}
               
            }
	}
    }
    public void createbasexml(){
	File dir = new File(xmldir+"result");
        dir.mkdir();
        DocumentBuilderFactory documentBuilderFactory;
        DocumentBuilder documentBuilder;
        try {
            documentBuilderFactory = DocumentBuilderFactory.newInstance();
            documentBuilder = documentBuilderFactory.newDocumentBuilder();
            outputdoc = documentBuilder.newDocument();
	    docroot = outputdoc.createElement("OPINFOS");
            outputdoc.appendChild(docroot);
            for (int i = 0 ; i < nList.size(); i++){
    		Node node = nList.get(i);
		Element e1 = (Element) node;
	 	Element opinfo = outputdoc.createElement("OPINFO");
		Attr attr = outputdoc.createAttribute("ID");
		attr.setValue(Integer.toString(i));
		opinfo.setAttributeNode(attr);
		opinfo.appendChild(outputdoc.importNode(node,true));
		docroot.appendChild(opinfo);
	    }
            TransformerFactory transformerFactory = TransformerFactory.newInstance();
            Transformer transformer = transformerFactory.newTransformer();
            DOMSource source = new DOMSource(outputdoc);
            File wf = new File(dir, "base");
            if (!wf.exists())
                wf.createNewFile();
            transformer.setOutputProperty(OutputKeys.INDENT, "yes");
            StreamResult result = new StreamResult(wf);
            transformer.transform(source, result);
        }catch (Exception e){
            System.out.println("Cannot write a base xml file");
            e.printStackTrace();
            return ;
        }
        
    }
    public void msgcodestat(ArrayList<Integer> list){
        for (int x : list) {
            Node node = nList.get(x);
            Element e1 = (Element) node;
            if (hashMsgSending.get(e1.getElementsByTagName("OPVAL").item(0).getTextContent()) == null) {
                hashMsgSending.put(e1.getElementsByTagName("OPVAL").item(0).getTextContent(), new ArrayList<Integer>());
            }
            hashMsgSending.get(e1.getElementsByTagName("OPVAL").item(0).getTextContent()).add(x);
        }
    }
    public void buildsyncgraph() {
	//eventremovethreadorder();
        eventcaller = new ArrayList<Integer>(nList.size());
        for (int i = 0 ; i < nList.size(); i++)
            eventcaller.add(-1);
        if (typeref.get("MsgSending") != null) {
            msgcodestat(typeref.get("MsgSending"));
            //msgcodestat(typeref.get("MsgProcEnter"));
            //msgcodestat(typeref.get("MsgProcExit"));

            for (String st : typeref.keySet())
                System.out.println(st + " : " + typeref.get(st).size());
            int hashsum = 0;
            for (String st : hashMsgSending.keySet()) {
                if (hashMsgSending.get(st).size() > 2) {
                    hashsum += hashMsgSending.get(st).size();
                    //int xx = hashMsg.get(st).get(0);
                    //int yy = hashMsg.get(st).get(1);
                    //System.out.println(st + " : " + hashMsg.get(st).size() +" "+ idplist.get(xx).pid + "-"+idplist.get(xx).tid
                    //+ " " + idplist.get(yy).pid+"-"+idplist.get(yy).tid);
                    //System.out.println(st + " : " + hashMsg.get(st).size());

               }else{
		    hashsum++;
	       }
            }
            System.out.println("TOTAL = " + hashsum);
        }
        if (typeref.get("MsgProcEnter") != null){
            ArrayList<Integer> list = typeref.get("MsgProcEnter");
            for (int x : list) {
                Node node = nList.get(x);
                Element e1 = (Element) node;
                if (hashMsgProcEnter.get(e1.getElementsByTagName("OPVAL").item(0).getTextContent()) == null) {
                    hashMsgProcEnter.put(e1.getElementsByTagName("OPVAL").item(0).getTextContent(), new ArrayList<Integer>());
                }
                hashMsgProcEnter.get(e1.getElementsByTagName("OPVAL").item(0).getTextContent()).add(x);
            }
        }

        /***** build thread creation and enter relation *****/

        //for (int i = 0 ; i < nList.size(); i++){
        int threadcreaterel = 0;
        for( int i : typeref.get("ThdCreate")){
            // introducing rule
            Node node = nList.get(i);
            Element e1 = (Element) node;
            //if (e1.getElementsByTagName("OPTY").item(0).getTextContent().equals("ThdCreate")){

            String tid = e1.getElementsByTagName("OPVAL").item(0).getTextContent();
	    int f = 0;
                //for (int j = 0 ; j <nList.size(); j++){
            for (int j : typeref.get("ThdEnter")){
                Node node2 = nList.get(j);
                Element e2 = (Element) node2;
                //System.out.println(idplist.get(j).pid+"-"+idplist.get(j).tid+" "+e2.getElementsByTagName("OPVAL").item(0).getTextContent());
                if (e2.getElementsByTagName("OPVAL").item(0).getTextContent().equals("-")) continue;
                String [] opval = e2.getElementsByTagName("OPVAL").item(0).getTextContent().split("/");
                //System.out.println(opval[0] + " "+ opval[1]);
                //if ( (e2.getElementsByTagName("OPTY").item(0).getTextContent().equals("ThdEnter"))&&
                if (( opval[1].equals(tid) || opval[0].equals(tid) )
                        &&(idplist.get(i).pid == idplist.get(j).pid)){
		    if (f > 0 ) {
				System.out.println(tid+" find multi children");
				break;
			} 
                    threadcreaterel ++;
                    System.out.println("Thread owner relation " + i +":" + idplist.get(i).pid+"-"+idplist.get(i).tid + " create " + j +":"+idplist.get(j).pid+"-"+idplist.get(j).tid);
                    addedge(i,j,1);
		    //System.out.println(i + " creates "+ j + "thread");
		    f++;			
                }

            }
            }
        System.out.println(threadcreaterel + "thread creation relation added ,expect " +typeref.get("ThdCreate").size());
       
	/* plug no creator thread to its direct parent*/
        for ( int i : typeref.get("ThdEnter")){
            if ((backedge.get(i).size()==0)&&(i>0)) {
		int xx = idplist.get(i-1).tid;
		int yy = idplist.get(i-1).pid;
		int x  = idplist.get(i).tid;
		int y  = idplist.get(i).pid;
		if ((x == xx) &&(y == yy)){
			System.out.println(i+" is no creator thread, plug it to its direct parent");
			addedge(i-1,i,1);
		}
	    }
	
        }
        /***** build thread join with a thread end          *****/

        int threadjoinrel = 0;
        for (int i : typeref.get("ThdJoin")){
            Node node = nList.get(i);
            Element e1 = (Element) node;
            int test = -1;
            //if (e1.getElementsByTagName("OPTY").item(0).getTextContent().equals("ThdCreate")){
            int pid = idplist.get(i).pid;
            String tid = e1.getElementsByTagName("OPVAL").item(0).getTextContent();
            for (int j : typeref.get("ThdExit")){
                IdPair idPair = idplist.get(j);
                if ((idPair.pid == pid)&&(idPair.tid == Integer.parseInt(tid))){
                    addedge(j,i,10); //
		    System.out.println(j + " join to "+ i);
                    test = j;
                    threadjoinrel++;
                    break;
                }
            }
            if (test >= 0) {
                //System.out.println(idplist.get(test) + " join to "+ idplist.get(i));
            }
            else
                System.out.println("Cannot find "+pid+"-"+tid +"'s ThdExit");
        }
        System.out.println(threadjoinrel + "thread join relation added ,expect " +typeref.get("ThdJoin").size());


        /***** build Event process call and callee relation *****/

        int genevent = 0;
        int notfound = 0;
	//if (typeref.get("EventProcEnter")!=null){
	//System.out.println("eventPE = " + typeref.get("EventProcEnter"));
        for (int i : typeref.get("EventProcEnter")){

            Node node = nList.get(i);
            //System.out.println("++++ i=" + i + " "+ node);
            Element e1 = (Element) node;
            String es1 = e1.getElementsByTagName("OPVAL").item(0).getTextContent();
            //System.out.println(es1);
            String hscode = "";
            for (int ch = 0; (ch < es1.length())&&(es1.charAt(ch) >= '0') &&(es1.charAt(ch) <= '9') ; ch++){
                hscode = hscode + es1.charAt(ch);
            }
            //System.out.println("event hashcode = " + hscode);
            if (es1.contains("GenericEventHandler")) {
                //
                int callee = -1;
                int calleedepth = 999999;
                for (int j : typeref.get("EventProcEnter")){
                    Node node2= nList.get(j);
                    //System.out.println("----- " + j +" " + node2);
                    Element e2 = (Element) node2;
		    String opval2 = e2.getElementsByTagName("OPVAL").item(0).getTextContent();
                    if ((i != j) && opval2.contains(hscode) 
//				&& opval2.contains("!")
								){
                            //&&(calleedepth >depth)){
                        //calleedepth = depth;
                        callee = j;
			addedge(i,callee,2);
                        eventcaller.set(callee,i);
                        //break;
                    }
                }
                genevent++;
		/*
   		if (callee == -1){
   		    for (int j : typeref.get("EventProcEnter")){
                    Node node2= nList.get(j);
                    //System.out.println("----- " + j +" " + node2);
                    Element e2 = (Element) node2;
                    String opval2 = e2.getElementsByTagName("OPVAL").item(0).getTextContent();
                    if ((i != j) && opval2.contains(hscode)){
                            //&&(calleedepth >depth)){
                        //calleedepth = depth;
                        callee = j;
                        break;
                    }
                }
		}*/
                if (callee == -1) {
                    //System.out.println(genevent+" : " + i+" -> "+ j);
 //                   addedge(i,callee,2);
 //                   eventcaller.set(callee,i);
 //               }else{
		    
                    notfound ++;
                    System.out.println(e1.getElementsByTagName("OPVAL").item(0).getTextContent());
                    //System.out.println(i+"'s callee is not found");
                }
            }

        }
	 for (int i : typeref.get("EventCreate")){
            Node node = nList.get(i);
            Element e1 = (Element) node;
            String es1 = e1.getElementsByTagName("OPVAL").item(0).getTextContent();
            String hscode = "";
            for (int ch = 0; (ch < es1.length())&&(es1.charAt(ch) >= '0') &&(es1.charAt(ch) <= '9') ; ch++){
                hscode = hscode + es1.charAt(ch);
            }
            //if (es1.contains("GenericEventHandler")) {
                int callee = -1;
                int calleedepth = 999999;
                for (int j : typeref.get("EventProcEnter")){
                    Node node2= nList.get(j);
                    Element e2 = (Element) node2;
                    String opval2 = e2.getElementsByTagName("OPVAL").item(0).getTextContent();
                    if ((i != j) && opval2.contains(hscode)&& (!opval2.contains("GenericEventHandler"))
                                                                ){
                        callee = j;
                        addedge(i,callee,2);
                        eventcaller.set(callee,i);
			System.out.println(i + " is event putter of "+ callee);
                    }
                }
                genevent++;
                if (callee == -1) {
                    notfound ++;
                    System.out.println(e1.getElementsByTagName("OPVAL").item(0).getTextContent());
                }
            //}

        }

        System.out.println(notfound +" in "+genevent+ " is not found in event part");
	
        /***** build the Msg caller and callee relation*****/
	
        notfound = 0;
        int genmsg = 0;
        HashMap<IdPair,ArrayList<Integer>> count = new HashMap<IdPair, ArrayList<Integer>>();
        IdPair sender;
        ArrayList<IdPair> receiver = new ArrayList<IdPair>();
        for (String st : hashMsgSending.keySet()) {
            if (hashMsgSending.get(st).size() > 1) {
                System.out.println(st+" has multi senders");
                count.clear();
                sender = null;
                receiver.clear();
                ArrayList<Integer> list = hashMsgSending.get(st);
                for (Integer j : list) {
                    if (count.get(idplist.get(j))== null){
                        count.put(idplist.get(j),new ArrayList<Integer>());
                        count.get(idplist.get(j)).add(j);
                    }
                    else count.get(idplist.get(j)).add(j);
                }
                int multisender = 0;
                for (IdPair idPair : count.keySet()){
                    if (count.get(idPair).size() == 1) receiver.add(idPair);
                    else{
                        if (sender == null) sender = idPair;
                        else {
                            
                           // System.out.println(st + " cannot be processed multi-sender : " + sender + " + "+ idPair);
                           // multisender = 1;
                           // break;
                            

                            if (count.get(idPair).size() > count.get(sender).size()) {
                                receiver.add(sender);
                                sender = idPair;
                            }
                        }
                    }
                }
                if (multisender == 1) continue;
                if (sender == null) {
                    sender = receiver.get(0);
                    receiver.remove(0);
                }
                //System.out.println("sender = " + sender);
                //System.out.println("count map = " + count);
                int receiversum = 0;
                for (IdPair idPair :receiver){
                    receiversum += count.get(idPair).size();
                }
                if (receiversum == 0){
                    //handle the multi invocation of v1
                    if (hashMsgProcEnter.get(st) == null){
                        System.out.println(st+" No any receiver");
                        continue;
                    }
                    if (count.get(sender).size()!= hashMsgProcEnter.get(st).size()) {
                        System.out.println(st + " MR-V1  sender does not match receiver :" + count.get(sender).size() + " VS " + hashMsgProcEnter.get(st).size());
                        continue;
                    }
                    for ( int i = 0; i < count.get(sender).size()-1; i++)
                     if (idplist.get(hashMsgProcEnter.get(st).get(i)).pid!=idplist.get(hashMsgProcEnter.get(st).get(i+1)).pid){
                         System.out.println(st +" MR-V1 receiver is not in the same process ");
                         continue;
                     }
                    Collections.sort(count.get(sender));
                    Collections.sort(hashMsgProcEnter.get(st));
                    int loop = 0;
                    while (loop < count.get(sender).size()){
                        int xx = count.get(sender).get(loop);
                        int yy = hashMsgSending.get(st).get(loop);
                        if (!buildMsgSync(xx,yy))  notfound++;
                        genmsg++;
                        loop ++;
                    }
                    continue;
                }
                if (count.get(sender).size() != receiversum) {
                    System.out.println(st + " cannot be processed sender does not match receiver :" + count.get(sender).size() + " VS " + receiversum);
                    continue;
                }
                for (int i = 0 ; i < receiver.size()-1; i++){
                    if (receiver.get(i).pid != receiver.get(i+1).pid) {
                        System.out.println(st +" cannot be processed receiver is not in the same process ");
                    }
                }
                Collections.sort(count.get(sender));
                Collections.sort(receiver);
                int loop = 0;
                int receiveindex = 0;
                int receiveoffset = 0;
                while (loop < receiversum) {
                    int xx = count.get(sender).get(loop);
                    //int yy = count.get(receiver.get(loop)).get(0);

                    int yy = count.get(receiver.get(receiveindex)).get(receiveoffset);
                    if (receiveoffset == count.get(receiver.get(receiveindex)).size()-1) {
                        receiveindex ++;
                        receiveoffset = 0;
                    }else{
                        receiveoffset ++;
                    }

                    //System.out.println(st +" : "+xx+"->"+yy);
                    if (!buildMsgSync(xx,yy))  notfound++;
                    genmsg++;
                    loop ++;
                }

            }  // no use for now 
            else{
                int xx = hashMsgSending.get(st).get(0);
                int sum = 0;
                int yy =-1;
		if (st.startsWith("ZK") == false){
	                for (int y : typeref.get("MsgProcEnter")){
        	            Node node = nList.get(y);
                	    Element element = (Element) node;
	                    if (element.getElementsByTagName("OPVAL").item(0).getTextContent().equals(st)){
        	                if (sum == 0) {
                	            yy = y;
                        	    sum ++;
	                        }else {
        	                    System.out.println(st + " more than one receiver : " + yy + " " + y);
                	            continue;
                       		}
	                    }
        	        }
    	            if (sum > 0) {
        	            genmsg++;
                	    addedge(xx, yy, 3);
                    	    System.out.println(st +" : "+xx+"->"+yy);
			    if (mr || hb){
				int xt = xx+1;
				int yt = -1;
				int sumt =0;
				if (samethread(xt,xx)){
				for (int y : typeref.get("MsgProcExit")){
	                            Node node = nList.get(y);
        	                    Element element = (Element) node;
                	            if (element.getElementsByTagName("OPVAL").item(0).getTextContent().equals(st)){
                        	        if (sumt == 0) {
                                	    yt = y;
                               	 	    sumt ++;
                                	}else {
                               		     System.out.println(st + " more than one exit: " + yt+ " " + y);
                                    		continue;
                                	}
                            	    }
				}
				if (sumt > 0){
					addedge(yt, xt, 3);
					genmsg++;
                               		System.out.println(st + " exit " + yt + " to "+ xt);
				}
                        }
			}
                	}else {
                    	System.out.println(st + " message has no receiver ");
                	}
		} else {
		    /*
		    System.out.println(xx+" Processing "+st);
		    String [] opval = ZKSplit(st);
		    String t;
		    if (opval[1].equals("setData")) 
 			t = "NodeDataChanged";
		    else if (opval[1].equals("delete"))
			t = "NodeDeleted";
		    else if (opval[1].equals("create"))
			t = "NodeCreated";
		    else {
			System.out.println(st + " contains a unknown opval!");
			continue;
		    }
		    Long xtime = Long.parseLong(opval[0]);
		    Long ctime = (long)-1;
		    int tempy;
		    for (int y : typeref.get("MsgProcEnter")){
                        Node node = nList.get(y);
                        Element element = (Element) node;
			String yval = element.getElementsByTagName("OPVAL").item(0).getTextContent();
			if (yval.startsWith("ZK")== false) continue;
			String [] opval2 = ZKSplit(yval);
			if (opval2.length < 2 ) continue;
			System.out.println(y + " "  +opval2[0] + " "+ opval2[1]+ " "+ opval2[2]);
                        if (opval2[2].equals(opval[2]) && opval2[1].equals(t)){
			    Long ytime = Long.parseLong(opval2[0]);
			System.out.println(y + " "  +opval2[0] + " "+ opval2[1]+ " "+ opval2[2]);
            		    if ((ytime > xtime) && ((ytime < ctime) || (ctime == -1))){
				yy = y;
				ctime = ytime;
			    }
                        }
                    }
		    if (ctime > 0) {
                            genmsg++;
                            addedge(xx, yy, 3);
                        //System.out.println(st +" : "+xx+"->"+yy);
                        }else {
                        System.out.println(st + " message has no receiver ");
                        }		
		}
		
                sum = 0;
                yy = -1;
                for (int y : typeref.get("MsgProcExit")){
                    Node node = nList.get(y);
                    Element element = (Element) node;
                    if ((element.getElementsByTagName("OPVAL").item(0).getTextContent().equals(st))&&
                            ((idplist.get(y).tid != idplist.get(xx).tid)||(idplist.get(y).pid != idplist.get(xx).pid))){
                        if (sum == 0) {
                            yy = y;
                            sum ++;
                        }else {
                            System.out.println(st + " more than one end in receiver : " + yy + " " + y);
                            continue;
                        }
                    }
                }
                if (sum > 0) {
                    genmsg++;
                    int xt = xx+1;
                    if ((idplist.get(xt).pid == idplist.get(xx).pid)&&(idplist.get(xt).tid == idplist.get(xx).tid)) {
                        addedge(yy, xt, 30);
                        //System.out.println(st + " : " + yy + "->" + xt);
                    }
                }else {
                    System.out.println(st + " message has no callback ");
                }
		****/

		}
            }
        }
	if (hb) {
            System.out.println("HB msg Special process begins");
	    for (int x : typeref.get("MsgProcEnter")){
		Node nodex = nList.get(x);
                Element elementx = (Element) nodex;
		String st = elementx.getElementsByTagName("OPVAL").item(0).getTextContent();
		if (st.startsWith("ZK") == false) continue;
		//System.out.println(st);
		String [] opval = ZKSplit(st);
		if (opval.length < 3) continue; 
                String t="";
                if (opval[1].equals("NodeDataChanged")) 
                    t = "setData";
                else if (opval[1].equals("NodeDeleted"))
                    t = "delete";
                else if (opval[1].equals("NodeCreated"))
                    t = "create";

		Long xtime = Long.parseLong(opval[0]);
                Long ctime = (long)-1;
		int yy=-1;
		for (int y :typeref.get("MsgSending") ){
			Node node = nList.get(y);
                        Element element = (Element) node;
                        String yval = element.getElementsByTagName("OPVAL").item(0).getTextContent();
			if (yval.startsWith("ZK") == false) continue;
			String [] opval2 = ZKSplit(yval);
			if (opval2[2].equals(opval[2]) && opval2[1].equals(t)){
                            Long ytime = Long.parseLong(opval2[0]);
                        //System.out.println(y + " "  +opval2[0] + " "+ opval2[1]+ " "+ opval2[2]);
                            if ((ytime < xtime) && ((ytime > ctime) || (ctime == -1))){
                                yy = y;
                                ctime = ytime;
                           }
			}
		}
		if (ctime > 0) {
                            genmsg++;
                            addedge(yy, x, 3);
                        System.out.println("ZK Special : "+x+"->"+yy);
                        }else {
                        System.out.println(st + " message has no sender ");
               }
	    }
	}
        System.out.println(notfound + " is not found in " +genmsg+ " in msg part");

        /*
        flag = new int[nList.size()];
        for (int i = 0 ; i < nList.size(); i++){
            flag[i] = 1;
        }
        for (int i = 0 ; i < nList.size(); i++){
            for (Pair pair : edge.get(i)) {
                flag[pair.destination] = 0;
            }
        }
        for (int i = 0 ; i < nList.size(); i++){
            if (flag[i] == 1){
                if (root < 0) root = i;
                else System.out.println("Too many roots");
            }
        }*/
        for (int i = 0; i < nList.size(); i++){
            if (backedge.get(i).size() == 0) {
		int pidi = idplist.get(i).pid;
		int pclink = 0;
		for (int j : typeref.get("ProcessCreate")){
		    Node npc = nList.get(j);
		    Element epc = (Element) npc;
  		    String st = epc.getElementsByTagName("OPVAL").item(0).getTextContent();
		    if (pidi == Integer.parseInt(st)) {
			pclink = 1;
			addedge(j,i);
			System.out.println(j+" creates process "+st+" : "+i);
			break;
		    } 
		}
		if (pclink == 1) continue;
                Node node = nList.get(i);
                Element e = (Element) node;
		if (e.getElementsByTagName("OPTY").item(0).getTextContent().equals("MsgProcEnter")){	
		Node nn1 = nList.get(i-1);
		Element en1 = (Element) nn1; //Warn less conditions
		if (en1.getElementsByTagName("OPTY").item(0).getTextContent().equals("MsgProcEnter"))	{
		addedge(i-1,i);continue;
		}
	}
                if (e.getElementsByTagName("OPTY").item(0).getTextContent().equals("EventProcEnter")){         addedge(i-1,i); continue;}
                root.add(i);
	
                if (!e.getElementsByTagName("OPTY").item(0).getTextContent().equals("ThdEnter")){
                    System.out.println("There exits a thread "+ i+" starting with "+e.getElementsByTagName("OPTY").item(0).getTextContent());
                }
            }
        }
        System.out.println("Number of Roots is " + root.size() + " E num is "+ esum);
        //Collections.sort(root);
        //System.out.println("Roots is " + root);


    }
    public String [] ZKSplit(String st){
	int i;
	String [] s = new String[3];
	try {
	//s[0] = "22222";s[1] = "tttttt";s[2] = "333333333";
        String [] pi = st.split("/");
	if (pi.length <2) {
		//System.out.println(st + " is too short");
		return pi;
	}
	String path = pi[1];
	for (i =2 ; i < pi.length; i++)
		path = path + "/"+ pi[i];
        String time = "";
	i = 2;
	while ( (pi[0].charAt(i) <= '9') &&(pi[0].charAt(i)>='0')){
		time = time + pi[0].charAt(i);
		i++;
	}
	s[0] = time;
	s[1] = pi[0].substring(2+time.length());
	s[2] = path;
	} catch (Exception e){
		System.out.println(st + " cannot be splitted in ZKSplit");
		e.printStackTrace();
	}
	return s;
    }
    public boolean buildMsgSync(int xx, int yy){
        if (xx == yy) return true;
        int f = 0;
        Node node1 = nList.get(xx);
        Element e1 = (Element) node1;
                /*int pid1 = idplist.get(xx).pid;
                int tid1 = idplist.get(xx).tid;
                System.out.println("pid = "+ pid1 +" tid = "+tid1);*/
        for (int x : ptidref.get(idplist.get(yy))) {
            Node node2 = nList.get(x);
            Element e2 = (Element) node2;
            if ((x != yy) && (e2.getElementsByTagName("OPVAL").item(0).getTextContent().equals(
                    e1.getElementsByTagName("OPVAL").item(0).getTextContent()
            )) && (e2.getElementsByTagName("OPTY").item(0).getTextContent().equals("MsgProcEnter"))) {
                f=1;
                yy = x;
                break;
            }
        }
        Node node3 = nList.get(yy);
        Element e3 = (Element) node3;
        for (int x : ptidref.get(idplist.get(xx))) {
            Node node2 = nList.get(x);
            Element e2 = (Element) node2;
            if ((x != xx) && (e2.getElementsByTagName("OPVAL").item(0).getTextContent().equals(
                    e3.getElementsByTagName("OPVAL").item(0).getTextContent()
            )) && (e2.getElementsByTagName("OPTY").item(0).getTextContent().equals("MsgProcEnter"))) {
                f=2;
                xx = x;
                break;
            }
        }


        if (f == 1) {
            addedge(yy, xx, 3);
            //System.out.println(yy + "->" + xx);
        } else {
            if (f == 0) {
                System.out.println("Cannot find Msg caller and callee relation between "+xx + " and " + yy);
                return false;
            } else {
                addedge(xx, yy, 3);
                //System.out.println(xx + "->" + yy);
            }
        }
        return true;
    }
    public void addedge(int from , int to){
        Pair p1 = new Pair(from,2);
        Pair p2 = new Pair(to,2);
        edge.get(from).add(p2);
        backedge.get(to).add(p1);
        esum ++;
    }
    public void addedge(int from , int to, int type){
        // type :  1-> thread creation and enter,10 -> thread join, 2 -> Eventhandle caller and callee,20 -> event call back (no use) 3 -> Msgsender and Msgreceiver,30 -> rpc call back
        if ((type == 1)||(type == 2)||(type == 3)){
            //if (emlink.get(to ) != -1)
		//System.out.println(to + " has msg/event/thd parent already: " + emlink.get(to) + " , be set to " + from);
	    emlink.set(to,from);     
        }
	if (type == 3) 
	    msender.set(to,from);
//	syncedges.get(type).add(new EgPair(from,to));
        addedge(from , to);
    }
/*
    public void buildtreepic() {

        String gexfile = xmldir+".gexf";

        try {
            PrintWriter writer = new PrintWriter(gexfile, "UTF-8");
            writer.println("<?xml version=\"1.0\" encoding=\"UTF-8\"?>");
            writer.println("<gexf xmlns:viz=\"http:///www.gexf.net/1.1draft/viz\" version=\"1.1\" xmlns=\"http://www.gexf.net/1.1draft\">");
            writer.println("<meta lastmodifieddate=\"2010-03-03+23:44\">");
            writer.println("<creator>Gephi 0.9</creator>");
            writer.println("</meta>");
            writer.println("<graph defaultedgetype=\"directed\" idtype=\"string\" type=\"static\">");
            writer.println("<nodes count=\""+nList.size()+"\">");
            for (int i = 0 ; i < nList.size(); i++){
                Node node = nList.get(i);
                Element eElement = (Element) node;
                writer.println("<node id=\"" + i + "\" label=\"" + eElement.getElementsByTagName("OPTY").item(0).getTextContent() + "\"/>");
            }
            writer.println("</nodes>");
            writer.println("<edges count=\""+ esum +"\">");
            int eindex = 0;
            for (int i = 0; i < nList.size(); i++){
                ArrayList<Pair> list = edge.get(i);
                //for(int j = 0 ; j < list.size(); j++){
                for (Pair tj : list){
                    //System.out.println("gexf : " + i + " j = "+ j);
                    //Pair tj = list.get(j);
                    writer.println("<edge id=\""+ eindex +"\" source=\""+ i +"\" target=\""+ tj.destination +"\" weight=\""+ tj.otype+"\"/>");
                    eindex ++;
                }
            }
            writer.println("</edges>");
            writer.println("</graph>");
            writer.println("</gexf>");
            writer.close();
        } catch (Exception e){
            e.printStackTrace();
        }
    }
*/
    public void buildmemref(){

        for ( int i = 0 ; i< nList.size(); i++){
            Node node2 = nList.get(i);
            Element e2 = (Element) node2;
            if ((e2.getElementsByTagName("OPTY").item(0).getTextContent().equals("HeapWrite") ||
                    (e2.getElementsByTagName("OPTY").item(0).getTextContent().equals("HeapRead")))){
                String address = e2.getElementsByTagName("OPVAL").item(0).getTextContent();
                ArrayList<Integer> list = memref.get(address);
                if (list  == null){
                    list = new ArrayList<Integer>(nList.size());
                    memref.put(address, list);
                }
                list.add(i);
            }
        }
        //
        //System.out.println("HashMap :" + memref);
        //
    }

    public void buildreachset(){
        reach = new ArrayList<HashSet<Integer>>(nList.size());
        flag = new int[nList.size()];
        HashSet<Integer> treach;
        for (int i=0; i < nList.size(); i++) {
            treach = new HashSet<Integer>(nList.size());
            reach.add(treach);
            flag[i] = 1;
        }
        for (int x : root)
            travel(x);
        // print for debug
        //for (int i=0; i<nList.size(); i++) {
        //    System.out.println(reach.get(i));
        //}
        //
    }

    public void travel(int x){
        flag[x] = 0;
        for(Pair pair : edge.get(x)){

            if (flag[pair.destination] == 1) travel(pair.destination);
            //reach.get(x).addAll(reach.get(pair.destination));
            reach.get(x).add(pair.destination);
        }
        reach.get(x).add(x);
        //flag[x] = 0;
    }
    boolean canreach(int source, int target){
        if (source == target) return true;
        for (int x : reach.get(source))
            if (canreach(x,target)) return true;
        return false;
    }

    public void bindtoevent(){

    }
    /******** traditional vector clock implementation *****/
    public void findconcurrent(){
        initfile();
        int consum = 0;
        //System.out.println("Memory location is "+memref.keySet());
        for (String st : memref.keySet()){
            ArrayList<Integer> list = memref.get(st);
            if (list.size() > 1) {
               // System.out.println("Memory location " + st + " : " + list.size() + "   " + consum + " before analysis");//+" "+list);
            }
            //consum += list.size() * (list.size() -1) /2;
            if (!st.contains("c")) {
                for (int i = 0; i < list.size(); i++)
                    for (int j = i + 1; j < list.size(); j++)
                        if ((concurrent(list.get(i), list.get(j)))) {
                            //if ((typeref.get("HeapWrite").contains(i)) ||(typeref.get("HeapWrite").contains(j)))
                            Node node1 = nList.get(list.get(i));
                            Node node2 = nList.get(list.get(j));
                            Element e1 = (Element) node1;
                            Element e2 = (Element) node2;
                            if (e1.getElementsByTagName("OPTY").item(0).getTextContent().equals("HeapWrite")
                                    ||(e2.getElementsByTagName("OPTY").item(0).getTextContent().equals("HeapWrite"))) {

                                consum++;
                                //writefile(list.get(i), list.get(j));
                                /*
                                if ((typeref.get("HeapWrite").contains(i)) ||(typeref.get("HeapWrite").contains(j))) {
                                }else{
                                    System.out.println(typeref.get("HeapWrite"));
                                    System.out.println("i = "+ list.get(i) + " j = "+ list.get(j));

                                }*/

                            }
                            //System.out.println(consum + ": " + list.get(i) + "  " + list.get(j));
                        }
            }
        }
        System.out.println("Concurrent number is at most " + consum);
        //flushfile(consum);
    }

    public void buildvectorclock(){
        vectorclock = new ArrayList<HashMap <IdPair, Integer>>();
        ptidsyncref = new HashMap <IdPair, ArrayList<Integer>>();

        for (int i=0 ; i<nList.size(); i++) {
            vectorclock.add(new HashMap<IdPair, Integer>());
            for (IdPair idPair : ptidref.keySet()){
                vectorclock.get(i).put(idPair, 0);
            }
        }
        ArrayList<Integer> degree = new ArrayList<Integer>();
        ArrayList<Integer> regree = new ArrayList<Integer>();
        for (int i=0 ; i < nList.size(); i++) {
            degree.add(backedge.get(i).size());
            regree.add(0);
        }
        // init the thread internal order

        for (IdPair idpair : ptidref.keySet()){
            int index = 0;
            ptidsyncref.put(idpair, new ArrayList<Integer>());
            ArrayList<Integer> list = ptidref.get(idpair);
            for ( int j : list){
                Node node = nList.get(j);
                Element element = (Element) node;
                //sync node includes MsgSending MsgProcEnter EventProcEnter ThdCreate ThdEnter
                /*if ((element.getElementsByTagName("OPTY").item(0).getTextContent().equals("MsgSending"))||(element.getElementsByTagName("OPTY").item(0).getTextContent().equals("ThdCreate"))
                    ||(element.getElementsByTagName("OPTY").item(0).getTextContent().equals("MsgProcEnter"))||(element.getElementsByTagName("OPTY").item(0).getTextContent().equals("ThdEnter"))
                    ||(element.getElementsByTagName("OPTY").item(0).getTextContent().equals("EventProcEnter")))*/{
                    index ++;
                    ptidsyncref.get(idpair).add(j);
                }
                vectorclock.get(j).put(idpair,index);
            }
        }

        ArrayList<Integer> toposort = new ArrayList<Integer>();
        toposort.addAll(root);
        int [] vcf = new int [nList.size()];
	for ( int xx= 0; xx < nList.size(); xx++) vcf[xx]= 0;
        int sumn = 0;
        while (!toposort.isEmpty()){
            int x = toposort.get(0);
	    vcf[x] ++;
            toposort.remove(0);
            sumn++;
            for (Pair j : edge.get(x)){
                mergevector(j.destination,x);
                regree.set(j.destination,regree.get(j.destination) + 1);
                if (regree.get(j.destination) == degree.get(j.destination)) toposort.add(j.destination);
            }
        }
	
        System.out.println(sumn + " in " + nList.size() + " vectorclock is computed");
	for (int i =0 ; i < nList.size(); i++) 
	    if ((vcf[i] == 0)&& (backedge.get(i).size()==0)) System.out.print( i + " " );
	    //System.out.print(vcf[i] + " ");
//        System.out.println(vectorclock);
    }

    public void mergevector(int t, int s){
        for (IdPair idPair : ptidref.keySet()){
            int max = vectorclock.get(t).get(idPair);
            if (max < vectorclock.get(s).get(idPair)) max = vectorclock.get(s).get(idPair);
            vectorclock.get(t).put(idPair,max);
        }

    }

    public boolean concurrent(int t, int s){
        //System.out.println("computing " + vectorclock.get(t) +" and "+ vectorclock.get(s));
        int sum = 0;
        int flag = 0;
        for (IdPair idPair : ptidref.keySet()){
            int x = vectorclock.get(t).get(idPair) - vectorclock.get(s).get(idPair);
            if (flag * x < 0 ) return true;
            if (x != 0) {
                flag = x;
            }
            //System.out.println(x+" + "+flag + " + "+sum);
            sum += x;
        }

        if (sum == 0) return true;
        return false;
    }

    /******** used for output a xml file ****/
    public void writefile(int x, int y, int freq){
        Node nx = nList.get(x);
        Node ny = nList.get(y);
        Element ex = (Element) nx;
        Element ey = (Element) ny;
        Element opair = outputdoc.createElement("OperationPair");
        opair.appendChild(outputdoc.importNode(nx,true));
        opair.appendChild(outputdoc.importNode(ny,true));
	Attr attr = outputdoc.createAttribute("freq");
        attr.setValue(Integer.toString(freq));
        opair.setAttributeNode(attr);
        docroot.appendChild(opair);
    }
    	
    public void initfile(){
        DocumentBuilderFactory documentBuilderFactory;
        DocumentBuilder documentBuilder;
        try {
            documentBuilderFactory = DocumentBuilderFactory.newInstance();
            documentBuilder = documentBuilderFactory.newDocumentBuilder();
            outputdoc = documentBuilder.newDocument();
        }catch (ParserConfigurationException e){
            System.out.println("Cannot write output to a xml file");
            return ;
        }
        docroot = outputdoc.createElement("OperationPairs");
        outputdoc.appendChild(docroot);
        return ;
    }

    public void flushfile(int sum){
        Attr attr = outputdoc.createAttribute("Len");
        attr.setValue(Integer.toString(sum));
        docroot.setAttributeNode(attr);
        try {
            TransformerFactory transformerFactory = TransformerFactory.newInstance();
            Transformer transformer = transformerFactory.newTransformer();
            DOMSource source = new DOMSource(outputdoc);
            File wf = new File(xmldir+"-result");
            if (!wf.exists())
                wf.createNewFile();
            transformer.setOutputProperty(OutputKeys.INDENT, "yes");
            StreamResult result = new StreamResult(wf);
            transformer.transform(source, result);
        } catch (Exception e){
            e.printStackTrace();
            System.out.println(xmldir+"-result"+" cannot be written");
        }

    }

    /******** iteration and bit-indicator for flipped order detection *******/
    public void  eventremovethreadorder() {
        /*
        for (int i = 0 ; i < nList.size(); i++){
            Node node = nList.get(i);
            Element e = (Element) node;
            String  value = e.getElementsByTagName("OPVAL").item(0).getTextContent();
            if ((e.getElementsByTagName("OPTY").item(0).getTextContent().equals("EventProcEnter"))&&(!value.contains("GenericEventHandler"))){
                int j = i-1;
                Node node2 = nList.get(j);
                Element e2 = (Element) node2;
                if ((!e2.getElementsByTagName("OPTY").item(0).getTextContent().equals("EventProcEnter")) &&
                        (idplist.get(i).pid == idplist.get(j).pid) &&(idplist.get(i).tid== idplist.get(j).tid)){
                    removeedge(j,i);
                    //System.out.println(j + "->"+ i + " is removed from graph");
                }
            }
        }*/
	int sumremove =0;
        for (int i : typeref.get("EventProcEnter")) {
            if (eventcaller.get(i) >= 0) {
                int j = i - 1;
                if ((idplist.get(i).pid == idplist.get(j).pid) && (idplist.get(i).tid == idplist.get(j).tid)) {
                    removeedge(j, i);
		    sumremove ++;
                    //System.out.println(j + "->"+ i + " is removed from graph");
                }
            }
        }
        System.out.println(esum + " edges remains in graph, " + sumremove +" is removed");
    }
    public void removeedge(int x, int y){
         // remove edge x -> y
        int f =0;
        ArrayList<Pair> list= edge.get(x);
        for (int i = 0; i < list.size(); i++)
            if (list.get(i).destination == y){
                list.remove(i);
                esum--;
                f = 1;
                ArrayList<Pair> l2 = backedge.get(y);
                for (int j =0; j < l2.size(); j++){
                    if (l2.get(j).destination== x){
                        l2.remove(j);
                        return;
                    }
                }
                System.out.println("Dont find backedge from " + y + " to "+x + ", when removeing");
                break;
            }
        if (f ==0)
            System.out.println("Dont find edge from " + x + " to "+y + ", when removeing");
    }
    public void findflippedorder(){
        //eventremovethreadorder();
        eventend = new ArrayList<Integer>(nList.size());
        for (int i = 0 ; i < nList.size(); i++)
            eventend.add(-1);
        int callersum = 0;
        for (int i = 0; i < nList.size(); i++)
            if (eventcaller.get(i) > -1 ) callersum++;
        System.out.println("Caller sum is " + callersum);
        for (int i : typeref.get("EventProcEnter")) {
            Node node = nList.get(i);
            Element e = (Element) node;
            String val = e.getElementsByTagName("OPVAL").item(0).getTextContent();
            int f = 0;
            for (int j : typeref.get("EventProcExit")){
                Node node2 = nList.get(j);
                Element e2 = (Element) node2;
		if (val.contains("!"))
		{
		 String [] valt = e2.getElementsByTagName("OPVAL").item(0).getTextContent().split("!");
		 String [] vals = val.split("!");
		 if ((valt[0] == vals[0])&&(valt[2] == vals[2])){
		    eventend.set(i,j);
                    f = 1;
                    break;
		 }
		}else if (e2.getElementsByTagName("OPVAL").item(0).getTextContent().equals(val)){
                    eventend.set(i,j);
                    f = 1;
                    break;
                }
            }
            if (f == 0) {
//                System.out.println("One event : " + i + " misses its end ");
            }
        }
        reachbitset = new ArrayList<BitSet>(nList.size());
        for (int i =0 ; i< nList.size(); i++) {
            reachbitset.add(new BitSet(nList.size()));
        }

        int loop =0;
        do {
            System.out.println(loop + " time iteration for event atomic edges. esum = "+esum);
            computereachbitset();
            loop++;
            System.out.println("compute bit set finished");
        }while (addeventatomicedge()&&(loop<20));

        initfile();
        int consum = 0;
        //System.out.println("Memory location is "+memref.keySet());

	BufferedWriter cout = null;
        BufferedWriter sout = null;
	BufferedWriter mout = null;
	try {
            File simplefile =  new File(xmldir+"result","simple");
	    File medianfile = new File(xmldir+"result","median");
	    File complexfile = new File(xmldir+"result","complex");
	    cout = new BufferedWriter(new FileWriter(complexfile));
	    mout = new BufferedWriter(new FileWriter(medianfile));
	    sout = new BufferedWriter(new FileWriter(simplefile));
	} catch (Exception e){}

        for (String st : memref.keySet()){
            ArrayList<Integer> list = memref.get(st);
            int lsum = 0;
            //consum += list.size() * (list.size() -1) /2;
            //if (!st.contains("c")) {
            if (true) {
                for (int i = 0; i < list.size(); i++)
                    for (int j = i + 1; j < list.size(); j++)
                        if (flippedorder(list.get(i),list.get(j),st) && hbzkinit(list.get(i),list.get(j))) {
                            //if ((typeref.get("HeapWrite").contains(i)) ||(typeref.get("HeapWrite").contains(j)))
                            Node node1 = nList.get(list.get(i));
                            Node node2 = nList.get(list.get(j));
                            Element e1 = (Element) node1;
                            Element e2 = (Element) node2;
                            if (e1.getElementsByTagName("OPTY").item(0).getTextContent().equals("HeapWrite")
                                    ||(e2.getElementsByTagName("OPTY").item(0).getTextContent().equals("HeapWrite"))) {

                                consum++;
                                writeaddlist(list.get(i), list.get(j));
                                writeaddlist2(list.get(i), list.get(j));
				writetext(cout,list.get(i), list.get(j));
                                lsum++;
                                /*
                                if ((typeref.get("HeapWrite").contains(i)) ||(typeref.get("HeapWrite").contains(j))) {
                                }else{
                                    System.out.println(typeref.get("HeapWrite"));
                                    System.out.println("i = "+ list.get(i) + " j = "+ list.get(j));

                                }*/

                            }
                            //System.out.println(consum + ": " + list.get(i) + "  " + list.get(j));
                        }
                if ((list.size() > 1)&&(lsum > 0)) {
//                    System.out.println("Memory location " + st + " : " + list.size() + "  give " + lsum);//+" "+list);
                }
            }
        }
/*	if (hb) {
	    int temptimer = 0;
	    System.out.println("HB special write parse begins");
	    for (int i :typeref.get("HeapWrite") ){
		temptimer ++;
		//if (temptimer % 500 == 0) 
		System.out.println(temptimer+" HB special write-write parsed.");
		for (int j : typeref.get("HeapWrite")){
		    if ((i!=j) && (hbspecial(i,j))){
			consum++;
                        writeaddlist(i, j);
                        writetext(cout,i, j);
			System.out.println(i + "  "+ j);
                        //lsum++;
		    }
		}
		System.out.println(temptimer+" HB special write-read parsed.");
                for (int j : typeref.get("HeapRead")){
                    if ((i!=j) && (hbspecial(i,j))){
                        consum++;
                        writeaddlist(i, j);
                        writetext(cout,i, j);
			System.out.println(i + "  "+ j);
                        //lsum++;
                    }
                }

	    }
	}*/
	HashMap <Integer, ArrayList<IdPair>> sortingout = new HashMap <Integer, ArrayList<IdPair>>();
	for (IdPair idPair : outputlist.keySet()) {
//	    stasticalana(idPair.pid,idPair.tid, outputlist.get(idPair));
//          writefile(idPair.pid, idPair.tid, outputlist.get(idPair));
	    int freq = outputlist.get(idPair);
	    if (sortingout.get(freq) == null)
		sortingout.put(freq,new ArrayList<IdPair>());
	    sortingout.get(freq).add(idPair);
//          System.out.print(outputlist.get(idPair) + " ");
        }
	ArrayList<Integer> freqset = new ArrayList(sortingout.keySet());
	Collections.sort(freqset, Collections.reverseOrder());
	int remain = 0;
	int remainsum = 0;
        int oldgetcstate;
        int oldtwotrans;
   	int olduni3;
	for (int freq : freqset){
	    for (IdPair idPair : sortingout.get(freq)){
		oldgetcstate = unigetstate;
		oldtwotrans  = unitwotrans;
		olduni3      = uni3;
	        stasticalana(idPair.pid,idPair.tid, outputlist.get(idPair));
//		if ((oldgetcstate == unigetstate)&&(oldtwotrans == unitwotrans)&&(olduni3 == uni3)){
	                writefile(idPair.pid, idPair.tid, outputlist.get(idPair));
			writetext(sout,idPair.pid, idPair.tid);
			remain += 1;
			remainsum += outputlist.get(idPair);
//			}
		}
	}
	for (IdPair idPair : outputlist2.keySet()){
	    writetext(mout,idPair.pid, idPair.tid);
	}
	System.out.println("\nOrderflipped number is at most " + consum + ", only "+outputlist.keySet().size()+" is unique in simple, "+outputlist2.keySet().size() +" is unique in median.");
	System.out.println("getCurrentState + doTransition = " + getcurdotrans + " unique:"+unigetstate);
	System.out.println("doTransition + doTransition = " + twodotrans + " unique:" + unitwotrans);
	System.out.println("getheadroom + setheadroom unique:" + uni3);
	System.out.println("remaining "+ remainsum+" unique:"+remain);
//        flushfile(outputlist.keySet().size());
    }
public boolean hbspecial(int x, int y){
	//special Identity and flipped order for HBase
	if (reachbitset.get(x).get(y) || reachbitset.get(y).get(x)) return false;
        Node nx = nList.get(x);
	Node ny = nList.get(y);
	Element ex = (Element) nx;
	Element ey = (Element) ny;
	String valx = ex.getElementsByTagName("OPVAL").item(0).getTextContent();
	String valy = ey.getElementsByTagName("OPVAL").item(0).getTextContent();
	String [] valxs = valx.split("/");
	String [] valys = valx.split("/");
	if (valxs.length * valys.length == 0) return false;
	if (valxs.length != valys.length) return false;
	for (int ii =1; ii < valxs.length; ii++)
		if (!valxs[ii].equals(valys[ii])) return false;
	return true;
}
public boolean hbzkinit(int x, int y){
        //special Identity and flipped order for HBase
        if (reachbitset.get(x).get(y) || reachbitset.get(y).get(x)) return false;
        Node nx = nList.get(x);
        Node ny = nList.get(y);
        Element ex = (Element) nx;
        Element ey = (Element) ny;
        Element esx = (Element) ex.getElementsByTagName("Stacks").item(0);
        Element sx = (Element) esx.getElementsByTagName("Stack").item(0);
        String xmethod = sx.getElementsByTagName("Method").item(0).getTextContent();
        Element esy = (Element) ey.getElementsByTagName("Stacks").item(0);
        Element sy = (Element) esy.getElementsByTagName("Stack").item(0);
        String ymethod = sy.getElementsByTagName("Method").item(0).getTextContent();
        if ((xmethod.equals("setData")|| xmethod.equals("getData"))&& zkcreatelist.contains(y)){
            int mat= 0;
            for (int j : zkcreatelist)
                if (reachbitset.get(j).get(x)) mat++;
            if (mat>=0) return false;
        }
        if ((ymethod.equals("setData")|| ymethod.equals("getData"))&& zkcreatelist.contains(x)){
            int mat= 0;
            for (int j : zkcreatelist)
                if (reachbitset.get(j).get(y)) mat++;
            if (mat>=0) return false;
        }

        return true;
}

public void writetext(BufferedWriter bf , int x ,int y){
	try{
	//   bf.write(y);
	//   bf.write(x);
	//   bf.newLine();
	   bf.write(String.valueOf(x)+" " + String.valueOf(y)+"\n");
	   bf.write(String.valueOf(x));
	   int j = emlink.get(x);
	   int len = 10;
	   while (j > -1){
	        bf.write("<-"+j);
		j = emlink.get(j);
		len --;
		if (len ==0) break;
	   }
	   bf.write("<-"+String.valueOf(emlink2.get(x)));
	   bf.write("\n");

           bf.write(String.valueOf(y));
           j = emlink.get(y);
           len = 10;
           while (j > -1){
                bf.write("<-"+j);
                j = emlink.get(j);
                len --;
		if (len == 0) break;
           }
	   bf.write("<-"+String.valueOf(emlink2.get(y)));
	   bf.write("\n");
	
	   //String[] st = suggestion(x,y).split("-");
	   //bf.write(st[0]+"\n");
	   //bf.write(st[1]+"\n");
	   bf.flush();
	} catch (Exception e){}
}
public String suggestion(int x, int y){

    int i = x;
    int j = y;
    Element ei = null;
    Element ej = null;
    
    while(true){
	System.out.println("   "+i + " "+ j);
	if ((i==-1)||(j ==-1)) break;
	Node ni = nList.get(i);
	ei      = (Element) ni;
//        Element esi = (Element) ei.getElementsByTagName("Stacks").item(0);
//	Element si  = (Element) esi.getElementsByTagName("Stack").item(0);
	String tidi = ei.getElementsByTagName("TID").item(0).getTextContent();

        Node nj = nList.get(j);
        ej      = (Element) nj;
//        Element esj = (Element) ej.getElementsByTagName("Stacks").item(0);
//        Element sj  = (Element) esj.getElementsByTagName("Stack").item(0);
	String tidj = ej.getElementsByTagName("TID").item(0).getTextContent();
	
	if (tidi.equals(tidj)){
	    i = emlink.get(emlink.get(i));
	    j = emlink.get(emlink.get(j));
	    continue;
	}else{
	    int ti = emlink.get(i);
	    int tj = emlink.get(j);
	    System.out.println("        "+i + " "+ j);
	    if ((ti == -1) && (tj == -1)) break;
	    if (typeref.get("MsgProcEnter").contains(ti) && typeref.get("MsgProcEnter").contains(tj)){ 
	    Node nx = nList.get(ti);
	    Node ny = nList.get(tj);
	    Element ex = (Element) nx;
	    Element ey = (Element) ny;
	    Element esx = (Element) ex.getElementsByTagName("Stacks").item(0);
    	    Element esy = (Element) ey.getElementsByTagName("Stacks").item(0);
	    Element sx = (Element) esx.getElementsByTagName("Stack").item(0);
	    Element sy = (Element) esy.getElementsByTagName("Stack").item(0);
	    String xclass = sx.getElementsByTagName("Class").item(0).getTextContent();
	    String yclass = sy.getElementsByTagName("Class").item(0).getTextContent();
	    if (xclass.equals(yclass)){
		i = emlink.get(ti);
		j = emlink.get(tj);
		continue;
	    }
	}
		
	}
	break;
    }
    if ((i==-1)||(j ==-1)) return "No suggestion@No suggestion"
				+"!No suggestion@No suggestion";
    String sti = lastCallstack(i);
    String stj = lastCallstack(j);
    /*
    int ind = 0;
    Element esi = (Element) ei.getElementsByTagName("Stacks").item(0);
    while (true){
	Element si  = (Element) esi.getElementsByTagName("Stack").item(ind);
	if (si.getElementsByTagName("Line").item(0).getTextContent().equals("-1")){
	    ind++;
	    continue;
	}
	sti = i +" "
	    + si.getElementsByTagName("Class").item(0).getTextContent()  + " "
	    + si.getElementsByTagName("Method").item(0).getTextContent() + " "
	    + si.getElementsByTagName("Line").item(0).getTextContent();
	break;
    }
    ind = 0;
    Element esj = (Element) ej.getElementsByTagName("Stacks").item(0);
    while(true){
        Element sj  = (Element) esj.getElementsByTagName("Stack").item(ind);
	if (sj.getElementsByTagName("Line").item(0).getTextContent().equals("-1")){
            ind++;
            continue;
        }
        stj = j + " " 
	    + sj.getElementsByTagName("Class").item(0).getTextContent()  + " "
            + sj.getElementsByTagName("Method").item(0).getTextContent() + " "
            + sj.getElementsByTagName("Line").item(0).getTextContent();
	break;
    }*/
    String ai = "#";
    String aj = "#";
    if ((emlink.get(i)>-1)&&(emlink.get(emlink.get(i)) > -1)){
        int ti = emlink.get(emlink.get(i));
        String idi = getIdentity(nList.get(i));
        String idti = getIdentity(nList.get(ti));
        int oi = identity.get(idi);
        int oti = identity.get(idti);
        ai = lastCallstack(ti) + " " + oti + " vs " + oi;
    }
    if ((emlink.get(j)>-1)&&(emlink.get(emlink.get(j)) > -1)){
        int tj = emlink.get(emlink.get(j));
        String idj = getIdentity(nList.get(j));
        String idtj = getIdentity(nList.get(tj));
        int oj = identity.get(idj);
        int otj = identity.get(idtj);
        aj = lastCallstack(tj) + " " + otj + " vs " + oj;  
    }
    return sti+"@"+stj+"!"+ai+"@"+aj;

}
public String lastCallstack(int i){
    Node ni = nList.get(i);
    Element ei = (Element) ni;
    String sti = "";
    int ind = 0;
    Element esi = (Element) ei.getElementsByTagName("Stacks").item(0);
    while (true){
        Element si  = (Element) esi.getElementsByTagName("Stack").item(ind);
        if (si.getElementsByTagName("Line").item(0).getTextContent().equals("-1")){
            ind++;
            continue;
        }
        sti = i +" "
            + si.getElementsByTagName("Class").item(0).getTextContent()  + " "
            + si.getElementsByTagName("Method").item(0).getTextContent() + " "
            + si.getElementsByTagName("Line").item(0).getTextContent();
        break;
    }
    return sti;		
}

public void stasticalana(int x, int y, int freq) {
    Node nx = nList.get(x);
    Node ny = nList.get(y);
    Element ex = (Element) nx;
    Element ey = (Element) ny;
    Element esx = (Element) ex.getElementsByTagName("Stacks").item(0);
    Element esy = (Element) ey.getElementsByTagName("Stacks").item(0);
    Element sx = (Element) esx.getElementsByTagName("Stack").item(0);
    Element sy = (Element) esy.getElementsByTagName("Stack").item(0);
    String xmethod = sx.getElementsByTagName("Method").item(0).getTextContent();	
    String ymethod = sy.getElementsByTagName("Method").item(0).getTextContent();
    if ((xmethod.equals("getCurrentState"))||(ymethod.equals("getCurrentState"))) { getcurdotrans += freq; unigetstate++;}
    if ((xmethod.equals("doTransition"))&&(ymethod.equals("doTransition"))) { twodotrans += freq; unitwotrans ++;}
    if ((xmethod.equals("setHeadroom"))||(ymethod.equals("setHeadroom"))) { uni3 ++;}
}
public boolean xmlequal(int x, int y){
        Node nx = nList.get(x);
        Node ny = nList.get(y);
        Element ex = (Element) nx;
        Element ey = (Element) ny;

        String pidx = ex.getElementsByTagName("PID").item(0).getTextContent();
        String tidx = ex.getElementsByTagName("TID").item(0).getTextContent();
        String optyx = ex.getElementsByTagName("OPTY").item(0).getTextContent();
        String opvalx = ex.getElementsByTagName("OPVAL").item(0).getTextContent();
        Element esx = (Element) ex.getElementsByTagName("Stacks").item(0);
        String slenx = esx.getAttribute("Len");

        String pidy = ey.getElementsByTagName("PID").item(0).getTextContent();
        String tidy = ey.getElementsByTagName("TID").item(0).getTextContent();
        String optyy = ey.getElementsByTagName("OPTY").item(0).getTextContent();
        String opvaly = ey.getElementsByTagName("OPVAL").item(0).getTextContent();
        Element esy = (Element) ey.getElementsByTagName("Stacks").item(0);
        String sleny = esy.getAttribute("Len");
        //if ((!pidx.equals(pidy))||(!tidx.equals(tidy))||(!optyx.equals(optyy))||(!opvalx.equals(opvaly))
        if (!optyx.equals(optyy)
//                ||(!slenx.equals(sleny))
		)
            return false;
   //     for (int i = 0 ; i < Integer.parseInt(slenx); i++ ){
        for (int i = 0 ; i < 1; i++ ){
            Element sx = (Element) esx.getElementsByTagName("Stack").item(i);
            Element sy = (Element) esy.getElementsByTagName("Stack").item(i);

            String xclass = sx.getElementsByTagName("Class").item(0).getTextContent();
            String xmethod = sx.getElementsByTagName("Method").item(0).getTextContent();
            String xlen = sx.getElementsByTagName("Line").item(0).getTextContent();
            String yclass = sy.getElementsByTagName("Class").item(0).getTextContent();
            String ymethod = sy.getElementsByTagName("Method").item(0).getTextContent();
            String ylen = sy.getElementsByTagName("Line").item(0).getTextContent();

            if ((!xclass.equals(yclass))||(!xmethod.equals(ymethod))||(!xlen.equals(ylen)))
                return false;

        }

        return true;

    }
public boolean xmlequal2(int x, int y){
        Node nx = nList.get(x);
        Node ny = nList.get(y);
        Element ex = (Element) nx;
        Element ey = (Element) ny;

        String pidx = ex.getElementsByTagName("PID").item(0).getTextContent();
        String tidx = ex.getElementsByTagName("TID").item(0).getTextContent();
        String optyx = ex.getElementsByTagName("OPTY").item(0).getTextContent();
        String opvalx = ex.getElementsByTagName("OPVAL").item(0).getTextContent();
        Element esx = (Element) ex.getElementsByTagName("Stacks").item(0);
        String slenx = esx.getAttribute("Len");

        String pidy = ey.getElementsByTagName("PID").item(0).getTextContent();
        String tidy = ey.getElementsByTagName("TID").item(0).getTextContent();
        String optyy = ey.getElementsByTagName("OPTY").item(0).getTextContent();
        String opvaly = ey.getElementsByTagName("OPVAL").item(0).getTextContent();
        Element esy = (Element) ey.getElementsByTagName("Stacks").item(0);
        String sleny = esy.getAttribute("Len");
        //if ((!pidx.equals(pidy))||(!tidx.equals(tidy))||(!optyx.equals(optyy))||(!opvalx.equals(opvaly))
        if (!optyx.equals(optyy)
                ||(!slenx.equals(sleny))
                )
            return false;
        for (int i = 0 ; i < Integer.parseInt(slenx); i++ ){
        //for (int i = 0 ; i < 1; i++ ){
            Element sx = (Element) esx.getElementsByTagName("Stack").item(i);
            Element sy = (Element) esy.getElementsByTagName("Stack").item(i);

            String xclass = sx.getElementsByTagName("Class").item(0).getTextContent();
            String xmethod = sx.getElementsByTagName("Method").item(0).getTextContent();
            String xlen = sx.getElementsByTagName("Line").item(0).getTextContent();
            String yclass = sy.getElementsByTagName("Class").item(0).getTextContent();
            String ymethod = sy.getElementsByTagName("Method").item(0).getTextContent();
            String ylen = sy.getElementsByTagName("Line").item(0).getTextContent();

            if ((!xclass.equals(yclass))||(!xmethod.equals(ymethod))||(!xlen.equals(ylen)))
                return false;

        }

        return true;

    }

    public void writeaddlist(int x, int y){
        for (IdPair idPair : outputlist.keySet()){
            int i = idPair.pid;
            int j = idPair.tid;
            if ((xmlequal(i,x)&&(xmlequal(j,y)))||((xmlequal(i,y))&&(xmlequal(j,x)))){
                int freq = outputlist.get(idPair);
                outputlist.put(idPair,freq+1);
                //System.out.println("Find duplicated pair");
                return ;
            }
        }
        IdPair idPair1 = new IdPair(x,y);
        outputlist.put(idPair1,1);
   }
    public void writeaddlist2(int x, int y){
        for (IdPair idPair : outputlist2.keySet()){
            int i = idPair.pid;
            int j = idPair.tid;
            if ((xmlequal2(i,x)&&(xmlequal2(j,y)))||((xmlequal2(i,y))&&(xmlequal2(j,x)))){
                int freq = outputlist2.get(idPair);
                outputlist2.put(idPair,freq+1);
                return ;
            }
        }
        IdPair idPair1 = new IdPair(x,y);
        outputlist2.put(idPair1,1);

        //System.out.println("Find new pair");
    }

    public boolean flippedorder(int x, int y, String st) {
	IdPair ip1 = idplist.get(x);
	IdPair ip2 = idplist.get(y);
	//if (! ((ip1.pid == ip2.pid) && (ip1.tid != ip2.tid))) return false;  
	
	if ((ip1.pid != ip2.pid)&&(!st.contains("hbase")) ) return false;  
        if (reachbitset.get(x).get(y)) return false;
        if (reachbitset.get(y).get(x)) return false;
        return true;
    }
    public boolean addeventatomicedge(){
        int change = 0;
	int ec = 0;
	int mc = 0;
	/*
        for (IdPair idPair : ptideventref.keySet()){
            for (int i : ptideventref.get(idPair))
                for (int j : ptideventref.get(idPair)) {
                    if //((eventcaller.get(i) >= 0) && (eventcaller.get(j) >= 0) &&
                            ((eventend.get(i) >= 0) && (eventend.get(j) >= 0)) {
                        if ((i != j) && (!reachbitset.get(eventend.get(i)).get(j)) && (!reachbitset.get(eventend.get(j)).get(i)) &&
                                (eventcaller.get(i) >= 0) && (eventcaller.get(j) >= 0)) {
                            if (reachbitset.get(eventcaller.get(i)).get(eventcaller.get(j))) {
                                addedge(eventend.get(i), j);
                                //System.out.println("Event Atomic edge " + eventend.get(i) + "->" + j);
                                change++;ec++;
                            }
                            if (reachbitset.get(eventcaller.get(j)).get(eventcaller.get(i))) {
                                addedge(eventend.get(j), i);
                                //System.out.println("Event Atomic edge " + eventend.get(j) + "->" + i);
                                change++;ec++;
                            }
                        }
                    }
                }
        }
	*/
	for (int i :typeref.get("EventProcEnter") )
            for (int j :typeref.get("EventProcEnter") ){
		IdPair pi = idplist.get(i);
                IdPair pj = idplist.get(j);
                if ( ((pi.pid != pj.pid) ||(pi.tid != pj.tid)) ) continue;
		int sendi = eventcaller.get(i);
                int sendj = eventcaller.get(j);
                int exiti = eexit.get(i);
                int exitj = eexit.get(j);
		if ((sendi == -1) ||(sendj == -1) ||
		    (exiti == -1) ||(exitj == -1) || (i==j)) continue;
                if (reachbitset.get(exiti).get(j) || reachbitset.get(exitj).get(i) ) continue;
		if (reachbitset.get(sendi).get(sendj)){
                        addedge(exiti,j);
                        change++;ec++;
//			System.out.println(i+ " ~~~~~ "+j);
                }
                if (reachbitset.get(sendj).get(sendi)){
                        addedge(exitj,i);
                        change++;ec++;
                }
		
	}
	for (int i :typeref.get("MsgProcEnter") )
	    for (int j :typeref.get("MsgProcEnter") ){
		IdPair pi = idplist.get(i);
		IdPair pj = idplist.get(j);
		//if ( ((pi.pid != pj.pid) ||(pi.tid != pj.tid)) && (!mr) ) continue;
		if ( ((pi.pid != pj.pid) ||(pi.tid != pj.tid))) continue;
		//System.out.println("Loop for "+ i +" & "+ j);
		int sendi = msender.get(i);
		int sendj = msender.get(j);
		int exiti = mexit.get(i);
		int exitj = mexit.get(j);
		if ((sendi == -1) ||(sendj == -1)|| (i==j)) continue;
		//System.out.println("Loop for "+ i +" & "+ j);
		if (reachbitset.get(exiti).get(j) || reachbitset.get(exitj).get(i) ) continue;
//		System.out.println("Loop for "+ i +" & "+ j);
		if (mr){
                    Node nx = nList.get(i);
                    Node ny = nList.get(j);
                    Element ex = (Element) nx;
                    Element ey = (Element) ny;
                    Element esx = (Element) ex.getElementsByTagName("Stacks").item(0);
                    Element esy = (Element) ey.getElementsByTagName("Stacks").item(0);
                    Element sx = (Element) esx.getElementsByTagName("Stack").item(0);
                    Element sy = (Element) esy.getElementsByTagName("Stack").item(0);
                    String xclass = sx.getElementsByTagName("Class").item(0).getTextContent();
                    String yclass = sy.getElementsByTagName("Class").item(0).getTextContent();
                    if (!xclass.equals(yclass)) continue;
		    if (reachbitset.get(sendi).get(sendj)){
			addedge(exiti,j);
			change++;mc++;
		    }
                    if (reachbitset.get(sendj).get(sendi)){
                        addedge(exitj,i);
                        change++;mc++;
                    }
		}
		else{
		    if (reachbitset.get(sendi).get(sendj)){
                        addedge(exiti,j);
                        change++;mc++;
                    }
                    if (reachbitset.get(sendj).get(sendi)){
                        addedge(exitj,i);
                        change++;mc++;
                    }
		}
	}
	System.out.println("msg change = "+mc + "; event change = "+ec);
        if (change > 0) return true;
        else     return  false;
    }
    public void computereachbitset(){
        flag = new int[nList.size()];
        for ( int i = 0 ; i < nList.size(); i++) {
            reachbitset.get(i).clear();
            flag[i] = 1;
        }
        BitSet bs = new BitSet(nList.size());
        bs.clear();
        //Node node = nList.get(4743);
        //Element e = (Element) node;
        //System.out.println("Cycle 4743 := "+ e.getElementsByTagName("OPTY").item(0).getTextContent()
        //        + e.getElementsByTagName("OPVAL").item(0).getTextContent());
        for (int i: root) {
            play(i,0);
            bs.or(reachbitset.get(i));
            //System.out.println(i+" is finished");
        }
        boolean f = true;
        for (int i = 0 ; i < nList.size(); i++)
            f = f & bs.get(i);
        if (f) System.out.println("All vertices are covered");
        else System.out.println("Not all vertices are covered");
    }
    public void play(int x, int dep){
        if (flag[x] ==0) return;
	flag[x] = 0;
        ArrayList<Pair> list = edge.get(x);
	//if (list.size() >1)
//        System.out.println(x + " : deep = "+dep+ " e="+list.size());
        for (Pair pair : list){
            play(pair.destination,dep+1);
            reachbitset.get(x).or(reachbitset.get(pair.destination));
        }
        reachbitset.get(x).set(x);
//        flag[x] = 0;
        //System.out.println(x + " is passed");
    }
	
   public void queryhbrelation(String path){
	try {
	BufferedReader br = new BufferedReader(new FileReader(path));
	    String line = "";
	    while ((line = br.readLine())!=null){
		String [] eles = line.split(" ");
		int x = Integer.parseInt(eles[0]);
		int y = Integer.parseInt(eles[1]);
		if ((!reachbitset.get(x).get(y)) && (!reachbitset.get(y).get(x))) {
		String str = suggestion(x,y);
		String [] strs = str.split("!");
		String [] basic = strs[0].split("@");
		String [] adv   = strs[1].split("@");
                //System.out.println("str = "+str);
                System.out.println("Basic x : " + basic[0]);
                System.out.println("Basic y : " + basic[1]);
                System.out.println("Advance x : " + adv[0]);
                System.out.println("Advance y : " + adv[1]);
		System.out.println(x + " & " + y + " have no HB relation");
		continue;
	}
		if (reachbitset.get(x).get(y))
			System.out.println(x + " -> "+ y );
		if (reachbitset.get(y).get(x))
			System.out.println(x + " <- "+ y );
		
	    }
	} catch (Exception e){
		System.out.println("Query file open error");
		e.printStackTrace();
	}
   } 
}
