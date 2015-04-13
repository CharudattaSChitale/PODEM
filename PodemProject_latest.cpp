#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <iostream>

using namespace std;

#define HZ 100
#define RETURN '\n'
#define EOS '\0'
#define COMMA ','
#define SPACE ' '
#define TAB '\t'
#define COLON ':'
#define SEMICOLON ';'

#define SPLITMERGE 'M'

#define T_INPUT 1
#define T_OUTPUT 2
#define T_SIGNAL 3
#define T_MODULE 4
#define T_COMPONENT 5
#define T_EXIST 9
#define T_COMMENT 10
#define T_END 11

#define TABLESIZE 5000
#define MAXIO 5000
#define MAXMODULES 5000
#define MAXDFF 10560

#define GOOD 1
#define FAULTY 2
#define DONTCARE -1
#define ALLONES 0xffffffff

#define MAXlevels 10000
#define MAXIOS 5120
#define MAXFanout 10192
#define MAXFFS 40048
#define MAXGATES 100000
#define MAXevents 100000

#define TRUE 1
#define FALSE 0

#define EXCITED_1_LEVEL 1
#define POTENTIAL 2
#define LOW_DETECT 3
#define HIGH_DETECT 4
#define REDUNDANT 5

enum
{
    JUNK,           /* 0 */
    T_input,        /* 1 */
    T_output,       /* 2 */
    T_xor,          /* 3 */
    T_xnor,         /* 4 */
    T_dff,          /* 5 */
    T_and,          /* 6 */
    T_nand,         /* 7 */
    T_or,           /* 8 */
    T_nor,          /* 9 */
    T_not,          /* 10 */
    T_buf,          /* 11 */
    T_tie1,         /* 12 */
    T_tie0,         /* 13 */
    T_tieX,         /* 14 */
    T_tieZ,         /* 15 */
    T_mux_2,        /* 16 */
    T_bus,          /* 17 */
    T_bus_gohigh,   /* 18 */
    T_bus_golow,    /* 19 */
    T_tristate,     /* 20 */
    T_tristateinv,  /* 21 */
    T_tristate1     /* 22 */
};

// gateLevelCkt class
////////////////////////////////////////////////////////////////////////

class gateLevelCkt
{
    // circuit information
    int numgates;               // total number of gates (faulty included)
    int numpri;                 // number of PIs
    int numout;                 // number of POs
    int maxlevels;              // number of levels in gate level ckt
    int maxLevelSize;           // maximum number of gates in one given level
    int levelSize[MAXlevels];   // levelSize for each level
    int inputs[MAXIOS];
    int outputs[MAXIOS];
    int *gtype;                 // gate type
    short *fanin;               // number of fanin, fanouts
    short *fanout;
    int *levelNum;              // level number of gate
    int **inlist;               // fanin list
    int **fnlist;               // fanout list
    char *sched;                // scheduled on the wheel yet?
    unsigned int *value1;
    unsigned int *value2;       // good value of gate

//for podem
    unsigned int *faultValue1;
    unsigned int *faultValue2;        // faulty value of gate
    int *faultGate;             // Gate of current fault
    int *REplaceType;           // tye of replaced gate
    bool *StuckAt;              // gate substitution fault modelled as stuck at fault
    int *OriginalGateType;      //type of gate before replacing
    int *D_frontier;            // Array storing D-Frontier
    


    // for simulator
    int **levelEvents;          // event list for each level in the circuit
    int *levelLen;              // event list length
    int numlevels;              // total number of levels in wheel
    int currLevel;              // current level
    int *activation;            // activation list for the current level in circuit
    int actLen;                 // length of the activation list
    int *actFFList;             // activation list for the FF's
    int actFFLen;               // length of the actFFList

public:
    int numff;                  // number of FF's



    gateLevelCkt(char *);       // constructor

// simulator information
    void setupWheel(int, int);
    void insertEvent(int, int);
    int  retrieveEvent();
    void goodsim();             // logic sim (no faults inserted)
    

// Functions related to  PODEM
    void setupFaults();         // gate substitution faults modelled as stuck at faults and stored in an array
    void setDontCares();        // Applies Dont care to all gates
    void Podem(FILE *);      // calls PODEM for different faults
    bool backtrace(int,bool);   // Back-trace function
    bool podemREcursion(int,bool);  // execute PODEM to find vector
    bool CheckPathtoPO (int);       // check x-path from D-frontier to PO
    void faultsim();              // Faulty simulation
    void getobjective(int,bool);      // Get Objective function
    void getDFrontier(int);   // get d-frontier
    void replacegate(int,int);// Replaces the gate to insert fault in the circuit.
    bool checkInputsForExcitation(int);//to make sure that fault is getting excited
};



// Global Variables
int TotalFaults=0;
/////////////////////////////////////////////////////////////////////////
gateLevelCkt *circuit;
int OBSERVE, INIT0;
char cktName[256];
bool isExcited =false;
bool isDetected =false;
int count1;
bool pathFound=false;
int myobjective;
bool objvalue;
int backTraceGate;
bool key=true;
int podemcounter=1;
int myCount;
int detectedCount=0;




inline void gateLevelCkt::insertEvent(int levelN, int gateN)
{

    levelEvents[levelN][levelLen[levelN]] = gateN;
    levelLen[levelN]++;
}

// constructor: reads in the *.lev file for the gate-level ckt
gateLevelCkt::gateLevelCkt(char *cktName)
{
    //cout<<"inside circuit constructor\n";
    FILE *yyin;
    char fName[256];
    int i, j, count;
    char c;
    int netnum, junk;
    int f1, f2, f3;
    int levelSize[MAXlevels];
    numff = 0;
    strcpy(fName, cktName);
    strcat(fName, ".lev");
    yyin = fopen(fName, "r");
    if (yyin == NULL)
    {
        fprintf(stderr, "Can't open .lev file\n");
        exit(-1);
    }

    numpri = numgates = numout = maxlevels = 0;
    maxLevelSize = 32;
    for (i=0; i<MAXlevels; i++)
        levelSize[i] = 0;

    fscanf(yyin, "%d", &count); // number of gates
    fscanf(yyin, "%d", &junk);

    // allocate space for gates
    gtype = new int[count];
    fanin = new short[count];
    fanout = new short[count];
    levelNum = new int[count];
    inlist = new int * [count];
    fnlist = new int * [count];
    sched = new char[count];
    value1 = new unsigned int[count];
    value2 = new unsigned int[count];
    faultValue1 = new unsigned int[count];
    faultValue2 = new unsigned int[count];
    
    
    D_frontier = new int[count];

    // now read in the circuit

    for (i=1; i<count; i++)
    {
        fscanf(yyin, "%d", &netnum);
        fscanf(yyin, "%d", &f1);
        fscanf(yyin, "%d", &f2);
        fscanf(yyin, "%d", &f3);

        numgates++;
        gtype[netnum] = (unsigned char) f1;
        f2 = (int) f2;
        levelNum[netnum] = f2;
        levelSize[f2]++;

        if (f2 >= (maxlevels))
            maxlevels = f2 + 5;
        if (maxlevels > MAXlevels)
        {
            fprintf(stderr, "MAXIMUM level (%d) exceeded.\n", maxlevels);
            exit(-1);
        }

        fanin[netnum] = (int) f3;
        if (f3 > MAXFanout)
            fprintf(stderr, "Fanin count (%d) exceeded\n", fanin[netnum]);

        if (gtype[netnum] == T_input)
        {
            inputs[numpri] = netnum;
            numpri++;
        }

        sched[netnum] = 0;

        
        inlist[netnum] = new int[fanin[netnum]];
        

        for (j=0; j<fanin[netnum]; j++)
        {
            fscanf(yyin, "%d", &f1);
            inlist[netnum][j] = (int) f1;
            
        }

        for (j=0; j<fanin[netnum]; j++)
        {
            fscanf(yyin, "%d", &f1);
            
        }

        
        fscanf(yyin, "%d", &f1);
        fanout[netnum] = (int) f1;

        if (gtype[netnum] == T_output)
        {
            outputs[numout] = netnum;
            numout++;
        }


        if (fanout[netnum] > MAXFanout)
            fprintf(stderr, "Fanout count (%d) exceeded\n", fanout[netnum]);

        fnlist[netnum] = new int[fanout[netnum]];
        for (j=0; j<fanout[netnum]; j++)
        {
            fscanf(yyin, "%d", &f1);
            fnlist[netnum][j] = (int) f1;
        }

        
        fscanf(yyin, "%d", &junk);
        
        while ((c = getc(yyin)) != '\n' && c != EOF)
            ;
    }   

    fclose(yyin);
    numgates++;
   
    for (i=0; i<maxlevels; i++)
    {
        if (levelSize[i] > maxLevelSize)
            maxLevelSize = levelSize[i] + 1;
    }

    printf("Successfully read in circuit:\n");
    printf("\t%d PIs.\n", numpri);
    printf("\t%d POs.\n", numout);
    printf("\t%d Dffs.\n", numff);
    printf("\t%d total number of gates\n", numgates);
    printf("\t%d levels in the circuit.\n", maxlevels / 5);

    setupWheel(maxlevels, maxLevelSize);
}




void gateLevelCkt::setupWheel(int numLevels, int levelSize)
{
    int i;

    numlevels = numLevels;
    levelLen = new int[numLevels];
    levelEvents = new int * [numLevels];
    for (i=0; i < numLevels; i++)
    {
    levelEvents[i] = new int[levelSize];
    levelLen[i] = 0;
    }
    activation = new int[levelSize];
    
    actFFList = new int[numff + 1];
}

////////////////////////////////////////////////////////////////////////
int gateLevelCkt::retrieveEvent()
{
    while ((levelLen[currLevel] == 0) && (currLevel < maxlevels))
        currLevel++;

    if (currLevel < maxlevels)
    {
        levelLen[currLevel]--;
        return(levelEvents[currLevel][levelLen[currLevel]]);
    }
    else
        return(-1);
}

////////////////////////////////////////////////////////////////////////
// goodsim() -
//  Logic simulate. (no faults inserted)
////////////////////////////////////////////////////////////////////////

void gateLevelCkt::goodsim()
{
    int sucLevel;
    int gateN, predecessor, successor;
    int *predList;
    int i;
    unsigned int val1, val2, tmpVal;
    //cout"f";

    currLevel = 0;
    actLen = actFFLen = 0;
    while (currLevel < maxlevels)
    {
        gateN = retrieveEvent();
        if (gateN != -1)    // if a valid event
        {
            sched[gateN]= 0;
            switch (gtype[gateN])
            {
            case T_and:
                val1 = val2 = ALLONES;
                predList = inlist[gateN];
                for (i=0; i<fanin[gateN]; i++)
                {
                    predecessor = predList[i];
                    val1 &= value1[predecessor];
                    val2 &= value2[predecessor];
                }
                break;
            case T_nand:
                val1 = val2 = ALLONES;
                predList = inlist[gateN];
                for (i=0; i<fanin[gateN]; i++)
                {
                    predecessor = predList[i];
                    val1 &= value1[predecessor];
                    val2 &= value2[predecessor];
                }
                tmpVal = val1;
                val1 = ALLONES ^ val2;
                val2 = ALLONES ^ tmpVal;
                break;
            case T_or:
                val1 = val2 = 0;
                predList = inlist[gateN];
                for (i=0; i<fanin[gateN]; i++)
                {
                    predecessor = predList[i];
                    val1 |= value1[predecessor];
                    val2 |= value2[predecessor];
                }
                break;
            case T_nor:
                val1 = val2 = 0;
                predList = inlist[gateN];
                for (i=0; i<fanin[gateN]; i++)
                {
                    predecessor = predList[i];
                    val1 |= value1[predecessor];
                    val2 |= value2[predecessor];
                }
                tmpVal = val1;
                val1 = ALLONES ^ val2;
                val2 = ALLONES ^ tmpVal;
                break;
            case T_not:
                predecessor = inlist[gateN][0];
                val1 = ALLONES ^ value2[predecessor];
                val2 = ALLONES ^ value1[predecessor];
                break;
            case T_buf:
                predecessor = inlist[gateN][0];
                val1 = value1[predecessor];
                val2 = value2[predecessor];
                break;
            case T_dff:
                predecessor = inlist[gateN][0];
                val1 = value1[predecessor];
                val2 = value2[predecessor];
                actFFList[actFFLen] = gateN;
                actFFLen++;
                break;
            case T_xor:
                predList = inlist[gateN];
                val1 = value1[predList[0]];
                val2 = value2[predList[0]];

                for(i=1; i<fanin[gateN]; i++)
                {
                    predecessor = predList[i];
                    tmpVal = ALLONES^(((ALLONES^value1[predecessor]) &
                                       (ALLONES^val1)) | (value2[predecessor]&val2));
                    val2 = ((ALLONES^value1[predecessor]) & val2) |
                           (value2[predecessor] & (ALLONES^val1));
                    val1 = tmpVal;
                }
                break;
            case T_xnor:
                predList = inlist[gateN];
                val1 = value1[predList[0]];
                val2 = value2[predList[0]];

                for(i=1; i<fanin[gateN]; i++)
                {
                    predecessor = predList[i];
                    tmpVal = ALLONES^(((ALLONES^value1[predecessor]) &
                                       (ALLONES^val1)) | (value2[predecessor]&val2));
                    val2 = ((ALLONES^value1[predecessor]) & val2) |
                           (value2[predecessor]& (ALLONES^val1));
                    val1 = tmpVal;
                }
                tmpVal = val1;
                val1 = ALLONES ^ val2;
                val2 = ALLONES ^ tmpVal;
                break;
            case T_output:
                predecessor = inlist[gateN][0];
                val1 = value1[predecessor];
                val2 = value2[predecessor];
                break;
            case T_input:
            case T_tie0:
            case T_tie1:
            case T_tieX:
            case T_tieZ:
                val1 = value1[gateN];
                val2 = value2[gateN];
                break;
            default:
                fprintf(stderr, "illegal gate type1 %d %d\n", gateN, gtype[gateN]);
                exit(-1);
            }   // switch

            // if gate value changed
            if ((val1 != value1[gateN]) || (val2 != value2[gateN]))
            {
                value1[gateN] = val1;
                value2[gateN] = val2;
                faultValue1[gateN]  = val1;
                faultValue2[gateN]  = val2;

                for (i=0; i<fanout[gateN]; i++)
                {
                    successor = fnlist[gateN][i];
                    sucLevel = levelNum[successor];

                    if (sched[successor] != 1)
                    {
                        if (sucLevel != 0)
                            insertEvent(sucLevel, successor);
                        else    // same level, wrap around for next time
                        {
                            activation[actLen] = successor;
                            actLen++;
                        }
                        sched[successor] = 1;
                    }
                }   // for (i...)
            }   // if (val1..)
        }   // if (gateN...)
    }   // while (currLevel...)

}

void gateLevelCkt::faultsim()
{
    int sucLevel;
    int gateN, predecessor, successor;
    int *predList;
    int i;
    unsigned int val1, val2, tmpVal;

    currLevel = 0;
    actLen = actFFLen = 0;
    while (currLevel < maxlevels)
    {
        gateN = retrieveEvent();
        if (gateN != -1)    // if a valid event
        {
            sched[gateN]= 0;
            switch (gtype[gateN])
            {
            case T_and:
                val1 = val2 = ALLONES;
                predList = inlist[gateN];
                for (i=0; i<fanin[gateN]; i++)
                {
                    predecessor = predList[i];
                    val1 &= faultValue1[predecessor];
                    val2 &= faultValue2[predecessor];
                }
                break;
            case T_nand:
                val1 = val2 = ALLONES;
                predList = inlist[gateN];
                for (i=0; i<fanin[gateN]; i++)
                {
                    predecessor = predList[i];
                    val1 &= faultValue1[predecessor];
                    val2 &= faultValue2[predecessor];
                }
                tmpVal = val1;
                val1 = ALLONES ^ val2;
                val2 = ALLONES ^ tmpVal;
                break;
            case T_or:
                val1 = val2 = 0;
                predList = inlist[gateN];
                for (i=0; i<fanin[gateN]; i++)
                {
                    predecessor = predList[i];
                    val1 |= faultValue1[predecessor];
                    val2 |= faultValue2[predecessor];
                }
                break;
            case T_nor:
                val1 = val2 = 0;
                predList = inlist[gateN];
                for (i=0; i<fanin[gateN]; i++)
                {
                    predecessor = predList[i];
                    val1 |= faultValue1[predecessor];
                    val2 |= faultValue2[predecessor];
                }
                tmpVal = val1;
                val1 = ALLONES ^ val2;
                val2 = ALLONES ^ tmpVal;
                break;
            case T_not:
                predecessor = inlist[gateN][0];
                val1 = ALLONES ^ faultValue2[predecessor];
                val2 = ALLONES ^ faultValue1[predecessor];
                break;
            case T_buf:
                predecessor = inlist[gateN][0];
                val1 = faultValue1[predecessor];
                val2 = faultValue2[predecessor];
                break;
            case T_dff:
                predecessor = inlist[gateN][0];
                val1 = faultValue1[predecessor];
                val2 = faultValue2[predecessor];
                actFFList[actFFLen] = gateN;
                actFFLen++;
                break;
            case T_xor:
                predList = inlist[gateN];
                val1 = faultValue1[predList[0]];
                val2 = faultValue2[predList[0]];

                for(i=1; i<fanin[gateN]; i++)
                {
                    predecessor = predList[i];
                    tmpVal = ALLONES^(((ALLONES^faultValue1[predecessor]) &
                                       (ALLONES^val1)) | (faultValue2[predecessor]&val2));
                    val2 = ((ALLONES^faultValue1[predecessor]) & val2) |
                           (faultValue2[predecessor] & (ALLONES^val1));
                    val1 = tmpVal;
                }
                break;
            case T_xnor:
                predList = inlist[gateN];
                val1 = faultValue1[predList[0]];
                val2 = faultValue2[predList[0]];

                for(i=1; i<fanin[gateN]; i++)
                {
                    predecessor = predList[i];
                    tmpVal = ALLONES^(((ALLONES^faultValue1[predecessor]) &
                                       (ALLONES^val1)) | (faultValue2[predecessor]&val2));
                    val2 = ((ALLONES^faultValue1[predecessor]) & val2) |
                           (faultValue2[predecessor]& (ALLONES^val1));
                    val1 = tmpVal;
                }
                tmpVal = val1;
                val1 = ALLONES ^ val2;
                val2 = ALLONES ^ tmpVal;
                break;
            case T_output:
                predecessor = inlist[gateN][0];
                val1 = faultValue1[predecessor];
                val2 = faultValue2[predecessor];
                break;
            case T_input:
            case T_tie0:
            case T_tie1:
            case T_tieX:
            case T_tieZ:
                val1 = faultValue1[gateN];
                val2 = faultValue2[gateN];
                break;
            default:
                fprintf(stderr, "illegal gate type1 %d %d\n", gateN, gtype[gateN]);
                exit(-1);
            }   // switch



            faultValue1[gateN] = val1;
            faultValue2[gateN] = val2;

            for (i=0; i<fanout[gateN]; i++)
            {
                successor = fnlist[gateN][i];
                sucLevel = levelNum[successor];
                if (sched[successor] == 0)
                {
                    if (sucLevel != 0)
                        insertEvent(sucLevel, successor);
                    else    // same level, wrap around for next time
                    {
                        activation[actLen] = successor;
                        actLen++;
                    }
                    sched[successor] = 1;
                }
            }   // for (i...)

        }   // if (gateN...)
    }   // while (currLevel...)
}

//code for PODEM
void gateLevelCkt::Podem(FILE * vecFile)
{
//cout<<"inside PODEM\n";
//cout<<"no of gates to be replaced"<<numgates<<"\n";
//cout<<faultGate[5];
//setDontCares();
for( myCount=0;myCount<TotalFaults;myCount++)
{
    setDontCares();
    //cout<<"gate no:"<<faultGate[i]<<"and gate type before replacing:"<<gtype[faultGate[i]]<<"\n";
    int oldTYpe=gtype[faultGate[myCount]];
    replacegate(faultGate[myCount],REplaceType[myCount]);
    //cout<<"gate type after replacing:"<<gtype[faultGate[i]]<<"\n";
    if(StuckAt[myCount]==0)
    {
        faultValue1[faultGate[myCount]] = 0;
        faultValue2[faultGate[myCount]] = 0;
    }
    else
    {
        faultValue1[faultGate[myCount]] = ALLONES;
        faultValue2[faultGate[myCount]] = ALLONES;
    }
    if((podemREcursion(faultGate[myCount],StuckAt[myCount])) == true)
       
    {
        //cout<<"\npodem detected the fault "<<faultGate[i]<<"stuck at" <<StuckAt[i];
        fprintf(vecFile, "\nfault: gate %d of type %d replaced by a gate of type %d\n",faultGate[myCount],oldTYpe,REplaceType[myCount]);
        for (int j = 1; j <= numpri; j++)
                    {
                        if (value1[j] && value2[j]){
                            //cout<<"\nvalue1"<<value1[j]<<"value2"<<value2[j];
                            fprintf(vecFile, "1");
                        }
                        else if ((value1[j] == 0) && (value2[j] == 0)){
                            //cout<<"\nvalue1"<<value1[j]<<"value2"<<value1[j];
                            fprintf(vecFile, "0");
                        }
                        else
                            fprintf(vecFile, "X");

                    }
                    fprintf(vecFile, "\n");
                    detectedCount++;
    }
    
    replacegate(faultGate[myCount],oldTYpe);

}
fprintf(vecFile,"Total number of faults :%d\n",TotalFaults);

fprintf(vecFile,"Total number of faults detected:%d\n",detectedCount);


}
//compute the D-frontier 
void gateLevelCkt::getDFrontier( int gate)
{
    
    //if(!isExcited)
       // return;
/*cout<<"\nvalue1[gate]"<<value1[gate];
cout<<"\nvval1[gate]"<<faultValue1[gate];
cout<<"\nvalue2[gate]"<<value2[gate];
cout<<"\nfval2[gate]"<<faultValue2[gate];*/

    if(((value1[gate] == 0 && value2[gate]) || (faultValue1[gate] == 0 && faultValue2[gate]) || (value1[gate] && value2[gate]==0) || (faultValue1[gate] && faultValue2[gate]==0) ))
    {
        D_frontier[count1]=gate;
        //cout<<"\ninside d-frontier";
        count1++;

    }

    else if((value1[gate] && value2[gate] && (faultValue1[gate] == 0) && (faultValue2[gate] == 0)) || (value1[gate] == 0 && value2[gate] == 0 && (faultValue1[gate]) && (faultValue2[gate])))
    {
        for(int i = 0; i <fanout[gate]; i++)
        {
            getDFrontier(fnlist[gate][i]);
        }
    }

    D_frontier[count1]=0;
}
//check if the x-path exists to PO
bool gateLevelCkt::CheckPathtoPO(int xgate){
    if(gtype[xgate]==2)
    {
    
    pathFound=true;
    return pathFound;
    }
    for(int i=0;i<fanout[xgate];i++)
    {
        if((value1[fnlist[xgate][i]] && !value2[fnlist[xgate][i]]) || (!value1[fnlist[xgate][i]] && value2[fnlist[xgate][i]])
            ||(faultValue1[fnlist[xgate][i]] && !faultValue2[fnlist[xgate][i]]) || (!faultValue1[fnlist[xgate][i]] && faultValue2[fnlist[xgate][i]]))
        {
           // cout<<"x available in one of the fanouts of dfrontier";
            CheckPathtoPO(fnlist[xgate][i]);
        }
    }
    return pathFound;

}
//getobjective function for exciting and propogating the fault
void gateLevelCkt::getobjective(int gate, bool value)
{
    objvalue=1;

    //cout<<"value1[gate]:"<<value1[gate]<<"\n";
    //cout<<"value2[gate]:"<<value2[gate]<<"\n";
    if(value1[gate] && !value2[gate]|| value2[gate]&& !value1[gate])
    {
        myobjective=gate;
        objvalue=!value;
        return;
    }

    //for(int i=0;i<count1;i++)
    //{
      //  cout<<"\n"<<D_frontier[i];
    //}
    int nextGate=D_frontier[0];
    for(int i=0;i<fanin[nextGate];i++)
    {
        if((value1[inlist[nextGate][i]] && !value2[inlist[nextGate][i]]) || (!value1[inlist[nextGate][i]] && value2[inlist[nextGate][i]]))
        {
            myobjective=inlist[nextGate][i];
        }
    }
        if(gtype[myobjective]==6 || gtype[myobjective]==7)
            objvalue=1;
        else if(gtype[myobjective]==8 || gtype[myobjective]==9)
            objvalue=0;
        return;
    
}
//backtrace to reach the PI
bool gateLevelCkt::backtrace(int gate, bool value)
{
    int num_inversion=0;
    while(gtype[gate]!=1)   
    {
        //cout<<"\n backtraced to"<<gate;
        if(gtype[gate]==7 || gtype[gate]==9 || gtype[gate]==10)
            num_inversion++;
         for(int i=0;i<fanin[gate];i++)
        {
            if((value1[inlist[gate][i]] && !value2[inlist[gate][i]]) || (value2[inlist[gate][i]] && !value1[inlist[gate][i]]))
            {
                //cout<<"found next gate\n"<<inlist[gate][i];
                gate=inlist[gate][i];
                break;
            }
        }


    }
    if(num_inversion%2!=0)
    {   //cout<<"checking\n";
        value=!value;
    }
    backTraceGate=gate;
    return value;
}

//Function to ensure that the fault is excited
bool gateLevelCkt::checkInputsForExcitation(int faultygate)
{
    if((OriginalGateType[myCount]==6 &&REplaceType[myCount]==7) || (OriginalGateType[myCount]==7 &&REplaceType[myCount]==6)
        || (OriginalGateType[myCount]==8 &&REplaceType[myCount]==9) || (OriginalGateType[myCount]==8 &&REplaceType[myCount]==9))
        return true;
    int onecount=0,zerocount=0;
    for(int i=0;i<fanin[faultygate];i++)
    {
        if(value1[inlist[faultygate][i]] && value2[inlist[faultygate][i]])
            onecount++;
        if(!value1[inlist[faultygate][i]] && !value2[inlist[faultygate][i]])
            zerocount++;

    }
    if(onecount>0 && zerocount>0)
        return true;
    else
        return false;
}

//PODEM algorithm for finding the inputs needed to detect the fault
bool gateLevelCkt::podemREcursion(int fgate, bool fvalue)
{

    count1=0;
    getDFrontier(fgate);
    isDetected=false;
    bool isPathAvailable=false;
    bool Cin;
    int successorGate;

    for(int i=0;i<numout;i++)
    {
        if((value1[outputs[i]] && value2[outputs[i]] && !faultValue1[outputs[i]] && !faultValue2[outputs[i]])
            ||(!value1[outputs[i]] && !value2[outputs[i]] && faultValue1[outputs[i]] && faultValue2[outputs[i]]))
        {

            isDetected=true;
            //cout<<"\nPODEM detected the fault "<<fgate<<"stuck at"<<fvalue;
            return true;
        }
    }
    for(int i=0;D_frontier[i]>0;i++)
    { //cout<<"D-frontier not empty\n";
        //cout<<"d-frontier not empty";
        if(CheckPathtoPO(D_frontier[i]))
        {
            //cout<<"path available\n";
            isPathAvailable=true;
            break;
        }
    }
    if(isPathAvailable)
    {
        //cout<<"path found\n";
        getobjective(fgate,fvalue);
        //cout<<"Objective"<<myobjective<<"="<<objvalue<<"\n";
        Cin=backtrace(myobjective, objvalue);
        //cout<<"backtraced to"<<backTraceGate<<"="<<Cin<<"\n";
        if( Cin == 0 )                                                // Assign values to PI
            {
                value1[backTraceGate] = 0;
                value2[backTraceGate] = 0;
                faultValue1[backTraceGate] = 0;
                faultValue2[backTraceGate] = 0;
            }
        else
            {
                value1[backTraceGate] = ALLONES;
                value2[backTraceGate] = ALLONES;
                faultValue1[backTraceGate] = ALLONES;
                faultValue2[backTraceGate] = ALLONES;
            }

        for(int i=0;i<fanout[backTraceGate];i++)
            {
             successorGate = fnlist[backTraceGate][i];
            if (sched[successorGate] == 0)
                {
                    insertEvent(levelNum[successorGate], successorGate);
                    sched[successorGate] = 1;
                }   
            }
            goodsim(); //simulating the value found by backtrace method
            key=checkInputsForExcitation(fgate);
            //cout<<"fgate:"<<fgate<<"\n";
            //cout<<"value1[fgate]:"<<value1[fgate]<<"\n";
            //cout<<"value2[fgate]:"<<value2[fgate]<<"\n";

            // inserting the fault. gate replacement fault is modelled as stuck at fault
        if(fvalue==1)
            {
                faultValue1[fgate] = 1;
                faultValue2[fgate] = 1;
            }
        else
            {
                faultValue1[fgate] = 0;
                faultValue2[fgate] = 0;
            }

        for(int i=0;i<fanout[fgate];i++)
            {
             successorGate = fnlist[fgate][i];
            if (sched[successorGate] == 0)
                {
                    insertEvent(levelNum[successorGate], successorGate);
                    sched[successorGate] = 1;
                }   
            }
            //simulating with faulty value at gate
            faultsim();
            //cout<<"here\n";
            //cout<<"fgate="<<fgate<<",fvalue="<<fvalue<<"\n";
            //cout<<"10="<<value1[10]<<","<<value2[10]<<"\n";
            //cout<<"10="<<faultValue1[10]<<","<<faultValue2[10]<<"\n";

            //cout<<"12="<<value1[12]<<","<<value2[12]<<"\n";
            //cout<<"12="<<faultValue1[12]<<","<<faultValue2[12]<<"\n";

            //cout<<"11="<<value1[11]<<","<<value2[11]<<"\n";

            //recursive call to podem for propogating the fault
            if(podemREcursion(fgate,fvalue) && key)
            {
                return true;
            }
            // wrong assignment at previous point so backtrack
            Cin=!Cin;
            if( Cin == 0 )                                                
            {
                value1[backTraceGate] = 0;
                value2[backTraceGate] = 0;
                faultValue1[backTraceGate] = 0;
                faultValue2[backTraceGate] = 0;
            }
        else
            {
                value1[backTraceGate] = ALLONES;
                value2[backTraceGate] = ALLONES;
                faultValue1[backTraceGate] = ALLONES;
                faultValue2[backTraceGate] = ALLONES;
            }

        for(int i=0;i<fanout[backTraceGate];i++)
            {
             successorGate = fnlist[backTraceGate][i];
            if (sched[successorGate] == 0)
                {
                    insertEvent(levelNum[successorGate], successorGate);
                    sched[successorGate] = 1;
                }   
            }
            goodsim();
            //key=checkInputsForExcitation(fgate);

            if(fvalue==1)
            {
                faultValue1[fgate] = 1;
                faultValue2[fgate] = 1;
            }
        else
            {
                faultValue1[fgate] = 0;
                faultValue2[fgate] = 0;
            }

        for(int i=0;i<fanout[fgate];i++)
            {
             successorGate = fnlist[fgate][i];
            if (sched[successorGate] == 0)
                {
                    insertEvent(levelNum[successorGate], successorGate);
                    sched[successorGate] = 1;
                }   
            }
            faultsim();

            if(podemREcursion(fgate,fvalue) && key)
            {
                return true;
            }

            value1[backTraceGate] = 0;
            value2[backTraceGate] = ALLONES;

            for(int i=0;i<fanout[backTraceGate];i++)
            {
             successorGate = fnlist[backTraceGate][i];
            if (sched[successorGate] == 0)
                {
                    insertEvent(levelNum[successorGate], successorGate);
                    sched[successorGate] = 1;
                }   
            }
            goodsim();
            //key=checkInputsForExcitation(fgate);

            if(fvalue==1)
            {
                faultValue1[fgate] = 1;
                faultValue2[fgate] = 1;
            }
            else
            {
                faultValue1[fgate] = 0;
                faultValue2[fgate] = 0;
            }

            for(int i=0;i<fanout[fgate];i++)
            {
             successorGate = fnlist[fgate][i];
            if (sched[successorGate] == 0)
                {
                    insertEvent(levelNum[successorGate], successorGate);
                    sched[successorGate] = 1;
                }   
            }
            faultsim();
            //cout<<"couldn't detect";
            return false;

        
    }
    else
    {
       // cout<<"couldn't detect. no xpath";
        return false;
    }

    
}




//all values are st to dont cares before starting PODEM
void gateLevelCkt::setDontCares()
{
    
    
    for (int i = 1; i <= numgates; i++)
    {
        value1[i] = 0;
        value2[i] = ALLONES;
        faultValue1[i] = 0;
        faultValue2[i] = ALLONES;

    }
}

//Inserting the fault by replacing the gate
void gateLevelCkt::replacegate(int gateno, int replaceTYpe)
{
    gtype[gateno]=replaceTYpe;
}

//store the modelled stuck at faults in arrays
void gateLevelCkt ::setupFaults()
{
    int n=numgates*2;
    faultGate=new int[n];
    REplaceType=new int[n];
    OriginalGateType=new int[n];
    StuckAt=new bool[n];
    int j=0;
    for(int i=1;i<numgates;i++)
    {
        if (gtype[i]==6 || gtype[i]==7 || gtype[i]==8 || gtype[i]==9)
        {   OriginalGateType[j]=gtype[i];
            OriginalGateType[j+1]=gtype[i];


            switch(gtype[i])
        {
            case 6:
            faultGate[j]=i;
            REplaceType[j]=8;
            StuckAt[j]=0;
            

            faultGate[j+1]=i;
            REplaceType[j+1]=7;
            StuckAt[j+1]=1;
            
            j=j+2;
            break;

            case 8:
            faultGate[j]=i;
            REplaceType[j]=6;
            StuckAt[j]=1;

            faultGate[j+1]=i;
            REplaceType[j+1]=9;
            StuckAt[j+1]=0;

            j=j+2;
            break;

            case 7:
            faultGate[j]=i;
            REplaceType[j]=9;
            StuckAt[j]=1;

            faultGate[j+1]=i;
            REplaceType[j+1]=6;
            StuckAt[j+1]=0;

            j=j+2;
            break;

            case 9:
            faultGate[j]=i;
            REplaceType[j]=7;
            StuckAt[j]=0;

            faultGate[j+1]=i;
            REplaceType[j+1]=8;
            StuckAt[j+1]=1;

            j=j+2;
            break;




        }
    }
    }
    TotalFaults=j;
}
//main method
int main(int argc, char *argv[])
{
FILE *vecFile;
int nameIndex= 1;
char cktName[256],detName[256],vecName[256];



strcpy(cktName, argv[nameIndex]);
strcpy(vecName, argv[nameIndex]);
strcat(vecName, ".vec");
circuit = new gateLevelCkt(cktName);

vecFile = fopen(vecName, "w");
circuit->setupFaults();
circuit->Podem(vecFile);
cout<<"\ndetected faults stored in .vec file\n";


}


