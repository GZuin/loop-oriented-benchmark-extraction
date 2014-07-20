#include "llvm/Pass.h"					/* Pass definition */
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"	/* raw_string_ostream */
#include <math.h>      					/* % */
#include <stdlib.h>     				/* srand, rand */
#include <time.h>       				/* time */
#include <fstream>						/* ofstream */
#include <string>						/* string */

//-load ../../llvm-3.4/Release+Asserts/lib/funextract.so -fextract

using namespace llvm;
using namespace std;

namespace 
{   struct FunctionExtractor : public ModulePass
    {

	static char ID;
	FunctionExtractor() : ModulePass(ID){}


	string fileId()
	{//Generates a random 6 characters string to differentiate beetween files with the same name
		string fileId="_";

		//Generate random seed
		srand(time(NULL));
		int i;

		//Fill fileId
		for(i=1; i<=5; ++i)
		{	//In the ASC table, numbers+letters go from 48 to 122
			char randomChar=rand()%72+48;

			//if char is :?@ etc
			if((randomChar>=58 && randomChar<=64) || (randomChar>=91 && randomChar<=96))
				randomChar+=7;

			fileId+=(randomChar);
		}
		return (fileId); //Ex.: "_F74t0"
	}
	
	virtual bool runOnModule(Module &M)
		{//Function analised all outtermost loops in the program and prints them in separete files
			for(Module::iterator F =M.begin(), E=M.end(); F!=E; ++F)
			{//Output file name of the loop extraction
				string filename=F->getName();
				filename+=fileId();
				ofstream outp;
				outp.open(filename.c_str(), ofstream::out);

				std::string str;
				llvm::raw_string_ostream rso(str);
				F->print(rso);
				outp<<rso.str()<<"\n";
				outp.close();
			}

	    	return (false);
		}//End runOnModule
    };//End struct
}//End namespace

char FunctionExtractor::ID=2;
static RegisterPass<FunctionExtractor> X("FunctionExtractor", "Function Extractor Pass",
                             false /* Only looks at CFG */,
                             false /* Analysis Pass */);
