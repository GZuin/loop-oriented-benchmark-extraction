#include "llvm/Pass.h"							//Pass info
#include "llvm/IR/Function.h"					//Function info
#include "llvm/Transforms/Utils/ValueMapper.h"	//VMap info
#include "llvm/Transforms/Utils/Cloning.h"		//CloneFunctionInto info
#include "llvm/Analysis/LoopPass.h"				//LoopBase info
#include "llvm/IR/Module.h"						//Module info
#include <vector>								//std::vector

using namespace llvm;
using namespace std;

//opt -load ../../llvm-3.4/Release+Asserts/lib/loopfun.so -loopfun

namespace {
  struct FunctionFromLoops : public ModulePass {
    static char ID;
    FunctionFromLoops() : ModulePass(ID) {}


   void getAnalysisUsage(AnalysisUsage &AU) const {
    	                        AU.addRequired<LoopInfo>();
    	                        AU.addPreserved<LoopInfo>();
    	                }


   bool cloneFunction (Function *OF, ValueToValueMapTy VMap)
   {//Create a new function clone
	   bool changed=false;
	   //Create function declaration
	   Function *NF = Function::Create(cast<FunctionType>(OF->getType()->getElementType()),
       OF->getLinkage(), "loopExtractionFun_" + OF->getName(), OF->getParent());
       NF->copyAttributesFrom(OF);
       //Insert entry on the VMAP
       VMap[OF] = NF;

       //The next section was copied from the cloneModule.cpp file, copies function body
       Function *F = cast<Function>(VMap[OF]);
       if (!OF->isDeclaration())
       {	Function::arg_iterator DestI = F->arg_begin();
            for (Function::const_arg_iterator J = OF->arg_begin(); J != OF->arg_end();++J)
            {	DestI->setName(J->getName());
           		VMap[J] = DestI++;
            }
            SmallVector<ReturnInst*, 8> Returns;  // Ignore returns cloned.
            CloneFunctionInto(F, OF, VMap, /*ModuleLevelChanges=*/true, Returns);
            changed=true;
       }
       return(changed);
   }

    virtual bool runOnModule(Module &M)
    {//Run over the program module
    	ValueToValueMapTy VMap;
    	bool changed=false;
        vector<Function*> scheduledToClone;
    	//Add a reference of the function to our 'scheduled to clone' vector
    	for(Module::iterator I=M.begin(), E=M.end(); I!=E ; ++I)
    	{	LoopInfo &LI = getAnalysis<LoopInfo>(*I);
    		//Clones the function l times, where l=number of loops inside the function
    		for (LoopInfo::iterator i = LI.begin(), e = LI.end(); i != e; ++i)
    		{	Loop *L=*i;
    			const vector<Loop*> &SubLoops = L->getSubLoops();
    			//Iterate trough the h-1 subLopps and then once more for the parent loop
    			for(unsigned int h=0; h<=SubLoops.size();++h)
    				scheduledToClone.push_back(I);

    		}
    	}
    	//Iterate trough our vector cloning functions
    	for(unsigned int i=0; i<scheduledToClone.size(); ++i)
    	{//Create a new function clone
    		Function *OF=scheduledToClone[i];
    		//Create function declaration
    		Function *NF = Function::Create(cast<FunctionType>(OF->getType()->getElementType()),
   		OF->getLinkage(), "loopExtractionFun_" + OF->getName(), OF->getParent());
    		NF->copyAttributesFrom(OF);
    	 	//Insert entry on the VMAP
    	     	VMap[OF] = NF;

    	       //The next section was copied from the cloneModule.cpp file, copies function body
    	       Function *F = cast<Function>(VMap[OF]);
    	       if (!OF->isDeclaration())
    	       {	Function::arg_iterator DestI = F->arg_begin();
    	            for (Function::const_arg_iterator J = OF->arg_begin(); J != OF->arg_end();++J)
    	            {	DestI->setName(J->getName());
    	           		VMap[J] = DestI++;
    	            }
    	            SmallVector<ReturnInst*, 8> Returns;  // Ignore returns cloned.
    	            CloneFunctionInto(F, OF, VMap, /*ModuleLevelChanges=*/true, Returns);
    	            changed=true;
    	       }
    	}

    	return(changed);
    }
  };
}

char FunctionFromLoops::ID = 0;
static RegisterPass<FunctionFromLoops> X("FunctionFromLoops", "Extract loops into functions Pass", false, false);
