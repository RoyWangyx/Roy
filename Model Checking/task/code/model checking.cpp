#include<fstream>
//#include<iostream>
#include<string>
#include<malloc.h>
using namespace std;
ifstream input("in.txt",ios::in);    //specify the input and output source
ofstream cout("out.txt",ios::out);
struct edge;
struct vertex;
typedef struct edge *pedge;
typedef struct vertex *pvertex;
struct edge
{
	int vex;
	pedge next;
};
struct vertex
{
	string name;							
	pedge lfirst,rfirst;					
};
struct graph       //use the structure graph to store the data of the original input
{
	int n;                                  
	int start;								
	vertex vex[101];						
};
struct LTLformula                                    //use a LTL structure for further process 
{
	int clmax,statemax,finalmax;         //final stands for the substring in the form of a until b
	string cl[51],final[10];              //cl[] denotes the substrings 
	bool state[101][51];                  //state denotes for each vertex, which of the substrings stored in cl are satisfied or violated
};
struct graph G;
void read()      //read the input document and construct a graph for storing data
{
	string s,s1,s2;
	getline(input,s);getline(input,s1);
	int i=-1,j=0;G.n=0;
	do
	{
		i++;
		if (s[i]==' '||s[i]=='\0')
		{
			G.n=G.n+1;
			G.vex[G.n].name=s.substr(j,i-j);
			G.vex[G.n].lfirst=NULL;
			G.vex[G.n].rfirst=NULL;
			if (G.vex[G.n].name==s1)G.start=G.n;
			j=i+1;			
	    }
	}while(s[i]!='\0');
    do 
    {
    	getline(input,s);
    	if (s!="")
    	{
    		i=0;
    		while(s[i]!=' ')
	        {
	        	i++;
		    }
		    j=i;i++;
		    while(s[i]!=' ')
	        {
	        	i++;
		    }
		    s1=s.substr(j+1,i-j-1);s2=s.substr(i+1);
		    i=1;j=1;
		    while (G.vex[i].name!=s1)i++;
		    while (G.vex[j].name!=s2)j++;
		    pedge p=G.vex[i].lfirst,q=p;
            while(p!=NULL){q=p;p=p->next;}            
		    p=pedge(malloc(sizeof(struct edge)));  
			if(G.vex[i].lfirst==NULL)G.vex[i].lfirst=p; else q->next=p;
            p->vex=j;p->next=NULL;
            p=G.vex[j].rfirst,q=p;
            while(p!=NULL){q=p;p=p->next;}            
		    p=pedge(malloc(sizeof(struct edge)));  
			if(G.vex[j].rfirst==NULL)G.vex[j].rfirst=p; else q->next=p;
            p->vex=i;p->next=NULL;
        }
    }while(s!="");
}
int* callastA(int a[])                 //backwards inference for 'all' symbol 
{
	int* b;
	b=(int*)malloc(sizeof(int)*(G.n+1));
    for (int i=1;i<=G.n;i++)b[i]=1; 
    for (int i=1;i<=G.n;i++)
    {
    	if (a[i]==0)
    	{
    		pedge p=G.vex[i].rfirst;
    		while (p!=NULL)
    		{
    			b[p->vex]=0;
    			p=p->next;
		    }
	    }
	}
	return b;
}
int* callastE(int a[])               //backwards inference for 'exists' symbol
{
	int* b;
	b=(int*)malloc(sizeof(int)*(G.n+1));
    for (int i=1;i<=G.n;i++)b[i]=0; 
    for (int i=1;i<=G.n;i++)
    {
    	if (a[i]==1)
    	{
    		pedge p=G.vex[i].rfirst;
    		while (p!=NULL)
    		{
    			b[p->vex]=1;
    			p=p->next;
		    }
	    }
	}
	return b;
}
int* calCTL(string s)         //core algorithm for backwards inference in CTL model checking
{
	if (s[0]=='!')
    {
    	int* a=calCTL(s.substr(2,s.size()-3));
    	for (int i=1;i<=G.n;i++)a[i]=1-a[i];
    	return a;
    }
    else if (s[0]=='(')     //processing brackets!
    {
    	int sum=1,i=0;
    	while (sum>0)
		{
			 i++;
		     if(s[i]=='(')sum++;
		     if(s[i]==')')sum--;
	    }
		int* a=calCTL(s.substr(1,i-1));
		int* b=calCTL(s.substr(i+3,s.size()-i-4));
		if(s[i+1]=='V')
		{
			for (int j=1;j<=G.n;j++)a[j]=1-(1-a[j])*(1-b[j]);
	    }
	    else
	    {
	    	for (int j=1;j<=G.n;j++)a[j]=a[j]*b[j];
	    }
	    return a;
    }
    else if (s[0]=='A')
    {
    	if (s[1]=='C')
    	{
    		int* a=calCTL(s.substr(2,s.size()-3));
			int* b;
    		b=callastA(a);
		    return b;
	    }
	    else if (s[1]=='D')
	    {
	        int f=1;
	        int* a=calCTL(s.substr(2,s.size()-3));
			int* b;
    		while (f==1)
	        {
	        	f=0;
	        	b=callastA(a);
	        	for (int i=1;i<=G.n;i++)
	        	{
	        		if (b[i]==1 && a[i]==0){a[i]=1;f=1;}
	            }
	        }
	        return a;
	    }
	    else if (s[1]=='S')
	    {
	    	int f=1;
	        int* a=calCTL(s.substr(2,s.size()-3));
			int* b;
    		while (f==1)
	        {
	        	f=0;
	        	b=callastA(a);
	        	for (int i=1;i<=G.n;i++)
	        	{
	        		if (b[i]==0 && a[i]==1){a[i]=0;f=1;}
	            }
	        }
	        return a;
	    }
	    else if (s[1]=='(')
	    {
	    	int sum=1,i=1;
    	    while (sum>0)
			{
				i++;
		    	if(s[i]=='(')sum++;
		     	if(s[i]==')')sum--;
	    	}
			int* a=calCTL(s.substr(2,i-2));
			int* b=calCTL(s.substr(i+3,s.size()-i-4));
			int* d;
		    int f=1;
    		while (f==1)
	    	{
	        	f=0;
	       	    d=callastA(b);
	        	for (int j=1;j<=G.n;j++)
	        	{
	        		if (a[j]==0)d[j]=0;
	           	}
	           	for (int j=1;j<=G.n;j++)
	        	{
	        		if (d[j]==1 && b[j]==0){b[j]=1;f=1;}
	           	}
	       	}
	      	if (s[i+1]=='U')
	      	{
			 	return b;
		    }
	 	    else if (s[i+1]=='W')
		    {
		    	int f=1;
    			while (f==1)
	    		{
	     	   		f=0;
	   	    	    d=callastA(a);
	        		for (int j=1;j<=G.n;j++)
	        		{
	        			if (d[j]==0 && a[j]==1){a[j]=0;f=1;}
	           		}
	       		}
	       		for (int j=1;j<=G.n;j++)
	       		{
	       			if (a[j]==1 ||b[j]==1)b[j]=1;
	       	    }
	       	    return b;
	  	    }
	    }
    }
    else if (s[0]=='E')
    {
    	if (s[1]=='C')
    	{
    		int* a=calCTL(s.substr(2,s.size()-3));
			int* b;
    		b=callastE(a);
		    return b;
	    }
	    else if (s[1]=='D')
	    {
	        int f=1;
	        int* a=calCTL(s.substr(2,s.size()-3));
			int* b;
    		while (f==1)
	        {
	        	f=0;
	        	b=callastE(a);
	        	for (int i=1;i<=G.n;i++)
	        	{
	        		if (b[i]==1 && a[i]==0){a[i]=1;f=1;}
	            }
	        }
	        return a;
	    }
	    else if (s[1]=='S')
	    {
	    	int f=1;
	        int* a=calCTL(s.substr(2,s.size()-3));
			int* b;
    		while (f==1)
	        {
	        	f=0;
	        	b=callastE(a);
	        	for (int i=1;i<=G.n;i++)
	        	{
	        		if (b[i]==0 && a[i]==1){a[i]=0;f=1;}
	            }
	        }
	        return a;
	    }
	    else if (s[1]=='(')
	    {
	    	int sum=1,i=1;
    	    while (sum>0)
			{
				i++;
		    	if(s[i]=='(')sum++;
		     	if(s[i]==')')sum--;
	    	}
			int* a=calCTL(s.substr(2,i-2));
			int* b=calCTL(s.substr(i+3,s.size()-i-4));
			int* d;
		    int f=1;
    		while (f==1)
	    	{
	        	f=0;
	       	    d=callastE(b);
	        	for (int j=1;j<=G.n;j++)
	        	{
	        		if (a[j]==0)d[j]=0;
	           	}
	           	for (int j=1;j<=G.n;j++)
	        	{
	        		if (d[j]==1 && b[j]==0){b[j]=1;f=1;}
	           	}
	       	}
	      	if (s[i+1]=='U')
	      	{
			 	return b;
		    }
	 	    else if (s[i+1]=='W')
		    {
		    	int f=1;
    			while (f==1)
	    		{
	     	   		f=0;
	   	    	    d=callastE(a);
	        		for (int j=1;j<=G.n;j++)
	        		{
	        			if (d[j]==0 && a[j]==1){a[j]=0;f=1;}
	           		}
	       		}
	       		for (int j=1;j<=G.n;j++)
	       		{
	       			if (a[j]==1 ||b[j]==1)b[j]=1;
	       	    }
	       	    return b;
	  	    }
	    }
    }
    else 
    {
		int *a;
		a=(int*)malloc(sizeof(int)*(G.n+1));
		for (int j=1;j<=G.n;j++)if (G.vex[j].name==s || s=="true")a[j]=1; else a[j]=0;
		return a;
    }
}
string simplify(string s)     //simplify the original LTL formula to get rid of W.S.D
{
	if (s[0]=='!' || s[0]=='C')return "!("+simplify(s.substr(2,s.size()-3))+")";
	else if (s[0]=='D')
	{
		string s1="(true)U"+s.substr(1);
		return simplify(s1);
    }
    else if (s[0]=='S')
    {
    	string s1="!(D(!"+s.substr(1)+"))";
    	return simplify(s1);
    }
    else if (s[0]=='(')   //processing brackets by the same virtue as before
    {
    	int sum=1,i=0;
    	while (sum>0)
		{
			i++;
		   	if(s[i]=='(')sum++;
		   	if(s[i]==')')sum--;
	    }
	    if (s[i+1]!='W')return "("+simplify(s.substr(1,i-1))+")"+s.substr(i+1,1)+"("+simplify(s.substr(i+3,s.size()-i-4))+")";
	    else
	    {
	    	string s1="(("+s.substr(1,i-1)+")U("+s.substr(i+3,s.size()-i-4)+"))V(S("+s.substr(1,i-1)+"))";
		    return simplify(s1);
	    }
    }
    else return s;
}
LTLformula initiatecl(string s)  //function for finding out all those legitimate substrings, initiating the structure LTLformula
{
	LTLformula L,L1,L2;
	L.finalmax=0;L1.finalmax=0;L2.finalmax=0;
	if (s[0]=='!')return initiatecl(s.substr(2,s.size()-3));
    else if(s[0]=='C')
    {
    	L=initiatecl(s.substr(2,s.size()-3));
    	L.clmax++;
    	L.cl[L.clmax]=s;
    	return L;
    }
	else if (s[0]=='(')
    {
    	int sum=1,i=0;
    	while (sum>0)
		{
			i++;
		   	if(s[i]=='(')sum++;
		   	if(s[i]==')')sum--;
	    }
	    L1=initiatecl(s.substr(1,i-1));
		L2=initiatecl(s.substr(i+3,s.size()-i-4));
		for (int j=1;j<=L2.clmax;j++)
		{
			int f=0;
			for (int k=1;k<=L1.clmax;k++)if(L1.cl[k]==L2.cl[j])f=1;
			if (f==0)
			{
				L1.clmax++;
				L1.cl[L1.clmax]=L2.cl[j];
		    }
	    }
	    for (int j=1;j<=L2.finalmax;j++)
		{
			int f=0;
			for (int k=1;k<=L1.finalmax;k++)if(L1.final[k]==L2.final[j])f=1;
			if (f==0)
			{
				L1.finalmax++;
				L1.final[L1.finalmax]=L2.final[j];
		    }
	    }
	    if (s[i+1]=='U')
	    {
		    L1.finalmax++;
		    L1.final[L1.finalmax]=s;
	    }
	    L1.clmax++;
    	L1.cl[L1.clmax]=s;
		return L1;
    }
    else
    {
    	L.clmax=1;
    	L.cl[1]=s;
    	return L;
    }
}
int findcl(string s,LTLformula L) //find the position of substring
{
	if (s[0]=='!')return -findcl(s.substr(2,s.size()-3),L);
	for (int i=1;i<=L.clmax;i++) if(L.cl[i]==s)return i;
	return 0;
}
LTLformula initiatestate(LTLformula L)  //cosntruct the set Q, paying attention to ruling out those impossible combinations
{
	int i;
	string s;
	bool state[101];
	for (i=1;i<=L.clmax+1;i++)state[i]=0;
	L.statemax=0;
	while(state[L.clmax+1]==0)
	{
		int f=0;
		for (int j=1;j<=L.clmax;j++)
		{
			s=L.cl[j];
			if (s=="false" && state[j]==1)f=1;
			if (s=="true" && state[j]==0)f=1;			
			if (s[0]=='(')
			{
				int sum=1;
				i=0;
    	        while (sum>0)
	         	{
		  	        i++;
		   	        if(s[i]=='(')sum++;
		   	        if(s[i]==')')sum--;
	            }
	            int x,y;
	            x=findcl(s.substr(1,i-1),L);
	            y=findcl(s.substr(i+3,s.size()-i-4),L);
	            if (x>0)x=state[x]; else x=1-state[-x];
	            if (y>0)y=state[y]; else y=1-state[-y];
	            if (s[i+1]=='V')
	            {
	               	if (state[j]==1 && x==0 && y==0)f=1;
	            	if ((state[j]==0) && (x==1 || y==1))f=1;
	            }
	            else if (s[i+1]=='^')
	            {
	            	if (state[j]==0 && x==1 && y==1)f=1;
	            	if ((state[j]==1) && (x==0 || y==0))f=1;
	            }
	            else if (s[i+1]=='U')
	            {
	            	if (state[j]==1 && y==0 && x==0)f=1;
	            	if (state[j]==0 && y==1)f=1;
	            }
	        }
	    }
	    if (f==0)
	    {
	       	L.statemax++;
	       	for (int j=1;j<=L.clmax;j++)L.state[L.statemax][j]=state[j]; 
	    }
	    i=1;
	    while(state[i]==1)
	    {
	    	state[i]=0;
	    	i++;
	    }
	    state[i]=1;
	}
	return L;
}
void judgeLTL(int point,int stateid,LTLformula L,int t,int g0[],int l0[],bool f0[][51][11],string roadto[][51],string loop[][51])
{        // find all loops, and judge which of those until syntaxs are satisfied 
	/*cout<<t<<endl;
	for (int j1=1;j1<=t;j1++)cout<<G.vex[g0[j1]].name<<" ";
	cout<<endl;*/
				
	for (int i=1;i<=L.clmax;i++)  // decide if the road can be joined to the current point and stateid
	{
		string s;
		s=L.cl[i];
		if (s[0]!='(' && s[0]!='C' && s!="true" && (s!=G.vex[point].name && L.state[stateid][i]==1 || s==G.vex[point].name && L.state[stateid][i]!=1))return;
    }
    t++;g0[t]=point;l0[t]=stateid;
    //cout<<t<<endl;
    if (roadto[point][stateid]=="S") // mark down the roadto information
    {
    	roadto[point][stateid]="";
    	for (int i=1;i<=t-1;i++)
    	{
    		roadto[point][stateid]=roadto[point][stateid]+G.vex[g0[i]].name+" ";
    	}
	}
    pedge p=G.vex[point].rfirst;
    while(p!=NULL) // the DFS searching process, use recursion to store relevant data
    {
    	for (int k=1;k<=L.statemax;k++)   //双重循环（while和k）枚举下一步搜索的位置
    	{
    		int f=0;
    		for (int j=1;j<=L.clmax;j++)          //j循环判断该位置能否合法到达，能f=0，不能f=1  
    		{
    			string s=L.cl[j];
    			if (s[0]=='C')                      
    			{
    				int x=findcl(s.substr(2,s.size()-3),L);
    				if(x>0)x=L.state[k][x]; else x=1-L.state[k][-x];
    				if (x==1 && L.state[stateid][j]==0)f=1;
    				if (x==0 && L.state[stateid][j]==1)f=1;
    			} 
    			else if (s[0]=='(')
				{
				    int sum=1;
				    int i=0;
    	        	while (sum>0)
	         		{ 
		  	        	i++;
		   	        	if(s[i]=='(')sum++;
		   	        	if(s[i]==')')sum--;
	            	}
	            	if (s[i+1]=='U')
	            	{
	            		int x,y,z;
	            		x=findcl(s.substr(1,i-1),L);
	            		y=findcl(s.substr(i+3,s.size()-i-4),L);
	            		z=findcl(s,L);
	            		if (x>0)x=L.state[k][x]; else x=1-L.state[k][-x];
	            		if (y>0)y=L.state[k][y]; else y=1-L.state[k][-y];
						if (z>0)z=L.state[k][z]; else z=1-L.state[k][-z];
						if (L.state[stateid][j]==1 && (y==0 && (x==0 || z==0)))f=1;
						if (L.state[stateid][j]==0 && (y==1 || (x==1 && z==1)))f=1;
				    }
				}
				if (f==1)break;
			}
			if (f==1)continue;
			int j=1;
			while ((p->vex!=g0[j] || k!=l0[j])&& j<=t)j++;	  //判断这个位置是否已经到达过（是否形成回路）
			if (j<=t)
			{
				int j0=j;
				string s1="";
				bool fplus[5001];
				for (int j1=1;j1<=t;j1++)fplus[j1]=0;
				for (int j1=j0;j1<=t;j1++)s1=s1+G.vex[g0[j1]].name+" ";  //将回路的节点保存在字符串s1中
				/*cout<<s1<<endl; 
				for (int j1=j0;j1<=t;j1++)
				{
					for (int j2=j0;j2<=L.clmax;j2++)cout<<L.state[l0[j1]][j2]<<" ";
					cout<<endl;
			    }*/
				for (;j<=t;j++)                         //判断有哪些F使得该回路中存在满足F的点
				{
					for (int j1=1;j1<=L.finalmax;j1++)
					{
						string s;
						s=L.final[j1];
						int sum=1;
				    	int i=0;
    	        		while (sum>0)
	         			{ 
		  	        		i++;
		   	        		if(s[i]=='(')sum++;
		   	        		if(s[i]==')')sum--;
	            		}
	            		int y,z;
	            		y=findcl(s.substr(i+3,s.size()-i-4),L);
	            		z=findcl(s,L);
	            		if (y>0)y=L.state[l0[j]][y]; else y=1-L.state[l0[j]][-y];
						if (z>0)z=L.state[l0[j]][z]; else z=1-L.state[l0[j]][-z];
				        if (z==0 || y==1)
				        {
				        	for (int j2=j0;j2<=t;j2++)
				        	{
				        		if (f0[g0[j2]][l0[j2]][j1]==0)       //如果该回路中使其中某点满足某个之前无法满足的F，就将该回路加入该点对应的loop数组中
				        		{
				        			f0[g0[j2]][l0[j2]][j1]=1;
				        			if(fplus[j2]==0)
				        			{
				        				fplus[j2]=1;
				        			    loop[g0[j2]][l0[j2]]=loop[g0[j2]][l0[j2]]+s1;
				        		    }
				        		}
				        	}
	            		}
	            	}
	            	if (L.finalmax==0 && f0[g0[j0]][l0[j0]][1]==0)  //如果表达式中没有F，需要记录下已经找到了一条合法的路径（回路）
	            	{
	            		f0[g0[j0]][l0[j0]][1]=1;
	            		loop[g0[j0]][l0[j0]]=s1;
	                }
	            }
	        }
	        else judgeLTL(p->vex,k,L,t,g0,l0,f0,roadto,loop);   //该位置合法且没有形成回路，则继续递归探索
	    }›4
		p=p->next;
    }
    t--;             //所有探索结束，回到之前状态并进行回溯
    return;
}
void calLTL(string s)   //main function for calculating LTL formula
{
	s=simplify(s);
	LTLformula L;
	L=initiatecl(s);
	L=initiatestate(L);
	int fp=0;
	for (int i=1;i<=L.statemax;i++)
	{
		int x=findcl(s,L);
		if(x>0)x=L.state[i][x]; else x=1-L.state[i][-x];
		//cout<<s<<endl;
		if (x==0)
		{
			int t=0,g0[5001],l0[5001]; //initialize the searching process for candidate status
			bool f0[101][51][11];
			string roadto[101][51],loop[101][51];
			for (int j=1;j<=G.n;j++)
			{
				for (int k=1;k<=L.statemax;k++)
				{
					roadto[j][k]="S";loop[j][k]="";
					for (int jk=1;jk<=L.finalmax+1;jk++)f0[j][k][jk]=0;
			    }
			}
			/*for (int j=1;j<=L.clmax;j++)
			{
				cout<<L.cl[j]<<" "<<L.state[i][j]<<endl;
		    }*/
		    judgeLTL(G.start,i,L,t,g0,l0,f0,roadto,loop);// search
		    int f;
		    for (int j=1;j<=G.n;j++)
			{
				for (int k=1;k<=L.statemax;k++)
				{
					f=1;
					for (int jk=1;jk<=L.finalmax;jk++)// check if our loop of counterexample satisfy all those infinite syntaxes
					{
						if (f0[j][k][jk]==0)f=0;
				    }
				    if (L.finalmax==0 && f0[j][k][1]==0)f=0; 
				    if (f==1)
				    {
				    	cout<<"false:";
				    	cout<<roadto[j][k]<<"("<<loop[j][k].substr(0,loop[j][k].size()-1)<<")"<<endl;
				    	fp=1;break;
				    }
			    }
			    if(fp==1)break;
			}
		    if(fp==1)break;
	    }
    }
    if (fp==0)cout<<"true"<<endl;
    return;
}
void demo()    //integrate the previous parts                                                                 // 
{
	read();
	string s;
	int f;
	while(getline(input,s))
	{
		int* a;
		if(s[0]=='C')
		{ 
	    	a=calCTL(s.substr(4));
			if (a[G.start]==1)cout<<"true"<<endl; else cout<<"false"<<endl;
	    }
	    else
	    {
	    	calLTL(s.substr(4)); 
	    }    
	}
    return;
}
int main()
{
	demo();  
    return 0;
}
