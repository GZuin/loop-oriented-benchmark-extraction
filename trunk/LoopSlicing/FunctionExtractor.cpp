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
	
	virtual bool runOnModule(Module &M)
		{//Function analised all outtermost loops in the program and prints them in separete files

		vector<Function*> scheduleToDelete;

		for(Module::iterator F =M.begin(), E=M.end(); F!=E; ++F)
			{//Output file name of the loop extraction
				string s=F->getName();
				string prefix="loopExtractionTrash";

				if(!(s.compare(0,prefix.size(),prefix)==0))
					continue;

				scheduleToDelete.push_back(F);

			}

			for(vector<Function*>::iterator it = scheduleToDelete.begin(); it!= scheduleToDelete.end(); it++)
			{	Function *foo = *it;
				foo->dropAllReferences();
				foo->eraseFromParent();
			}

	    	return (true);
		}//End runOnModule
    };//End struct
}//End namespace

char FunctionExtractor::ID=2;
static RegisterPass<FunctionExtractor> X("FunctionExtractor", "Leave only loopExtraction functions",
                             false /* Only looks at CFG */,
                             false /* Analysis Pass */);
