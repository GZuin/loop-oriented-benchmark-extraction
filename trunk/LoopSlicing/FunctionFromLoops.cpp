#include "llvm/Pass.h"							//Pass info
#include "llvm/IR/Function.h"					//Function info
#include "llvm/Transforms/Utils/ValueMapper.h"	//VMap info
#include "llvm/Transforms/Utils/Cloning.h"		//CloneFunctionInto info
#include "llvm/Analysis/LoopPass.h"				//LoopBase info
#include "llvm/IR/Module.h"						//Module info
#include "llvm/InstVisitor.h"
#include "llvm/Support/InstIterator.h"
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

   void cloneFunction(Function *OF)
   {//Create a clone from our old function, but with a void return type

   //Get the old function type, will be changed to void later
        FunctionType *FTy = OF->getFunctionType();
   //Get the parameters
        vector<Type*> Parameters(FTy->param_begin(), FTy->param_end());
   //New Function type
        FunctionType *NFTy = FunctionType::get(Type::getVoidTy(OF->getContext()), Parameters, OF->isVarArg());

   //Create NF declaration with the same linkage and the same attributes
        Function *NF = Function::Create(NFTy, OF->getLinkage());
        string name="loopExtractionFun_";
        name+=OF->getName();
        NF->setName(name);
   //Copy and set NF parameters
        NF->copyAttributesFrom(OF);
        Function::arg_iterator NFarg, OFarg, OFargEnd;
        for (NFarg = NF->arg_begin(), OF->arg_begin(), OF->arg_end(); OFarg != OFargEnd; ++OFarg, ++NFarg)
        	NFarg->setName(OFarg->getName());

   //Set VMap references
        ValueToValueMapTy VMap;
        Function::arg_iterator DestI = NF->arg_begin();
        for (Function::const_arg_iterator J = OF->arg_begin(); J != OF->arg_end();++J)
        { DestI->setName(J->getName());
          VMap[J] = DestI++;
        }
   //Ignore returns cloned
        SmallVector<ReturnInst*, 8> Returns;
   //Copy and prune function body
        CloneAndPruneFunctionInto(NF, OF, VMap, /*Module level changes*/false, Returns);
   //Change function return type to void
        voidReturn(NF);
   // Insert the function clone into the module
        OF->getParent()->getFunctionList().insert(OF, NF);
   }

   void voidReturn(Function* F)
   {// Substitute the return value instructions by return void
	   //Store all returns in the function
	   SmallPtrSet<ReturnInst*, 4> retSet;
	   for (inst_iterator inst = inst_begin(F), instend = inst_end(F); inst != instend; ++inst)
	   {	if(inst->isTerminator())
		   	{	if (ReturnInst* retInst = dyn_cast<ReturnInst>(&*inst))
        		{// Create the ret(void)
            		ReturnInst::Create(F->getContext(), 0, retInst);
            		// Insert the new return after the old return
            		retSet.insert(retInst);
        		}
		   	}
	   }

      //Remove old returns
	   for (SmallPtrSet<ReturnInst*, 4>::iterator i = retSet.begin(), ie = retSet.end(); i != ie; ++i)
		   (*i)->eraseFromParent();
   }


    virtual bool runOnModule(Module &M)
    {//Run over the program module
    	ValueToValueMapTy VMap;
    	bool changed=false;
        vector<Function*> scheduledToClone;
    	//Add a reference of the function to our 'scheduled to clone' vector
    	for(Module::iterator I=M.begin(), E=M.end(); I!=E ; ++I)
    	{	LoopInfo &LI = getAnalysis<LoopInfo>(*I);
    		//We want to clone the function l times, where l=number of loops inside the function
    		for (LoopInfo::iterator i = LI.begin(), e = LI.end(); i != e; ++i)
    		{	changed=true;
    			Loop *L=*i;
    			const vector<Loop*> &SubLoops = L->getSubLoops();
    			//Iterate trough the h-1 subLopps and then once more for the parent loop
    			for(unsigned int h=0; h<=SubLoops.size();++h)
    				scheduledToClone.push_back(I);
    		}
    	}
    	//Iterate trough our vector cloning functions
    	for(unsigned int i=0; i<scheduledToClone.size(); ++i)
    		cloneFunction(scheduledToClone[i]);

    	return(changed);
    }
  };
}

char FunctionFromLoops::ID = 0;
static RegisterPass<FunctionFromLoops> X("FunctionFromLoops", "Extract loops into functions Pass", false, false);
