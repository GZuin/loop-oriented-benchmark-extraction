#include "llvm/Pass.h"					/* Pass definition */
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"	/* raw_string_ostream */
#include "llvm/Transforms/Utils/ValueMapper.h"	//VMap info
#include "llvm/Transforms/Utils/Cloning.h"		//CloneFunctionInto info
#include <math.h>      					/* % */
#include <stdlib.h>     				/* srand, rand */
#include <time.h>       				/* time */
#include <fstream>						/* ofstream */
#include <string>						/* string */
#include "DepGraph.h"

//-load ../../llvm-3.4/Release+Asserts/lib/LoopSlicing.so -LoopSlicing

using namespace llvm;
using namespace std;

namespace
{   struct FunLoopSlicing : public FunctionPass
    {
    private:
		Graph* fullGraph;
		int loopcounter;
    public:
		Graph* depGraph;

	static char ID;
	FunLoopSlicing() : FunctionPass(ID){}


	void getAnalysisUsage(AnalysisUsage &AU) const{
		AU.addRequired<functionDepGraph> ();
		AU.addRequiredTransitive<LoopInfoEx> ();
		//AU.addRequiredTransitive<DominatorTree> ();
	    AU.setPreservesAll();
	}

	set<Value*> getLoopInputs(Loop *L, Graph *depGraph) {

		std::set<Value*> loopExitPredicates = getLoopExitPredicates(L);

	            std::set<GraphNode*> visitedNodes;
	            std::set<GraphNode*> workList;

	            for(std::set<Value*>::iterator v = loopExitPredicates.begin(); v != loopExitPredicates.end(); v++){
	                if (GraphNode* valueNode = depGraph->findNode(*v))
	                    workList.insert(valueNode);
	                else
	                    errs() << "Value not found in the graph : " << **v << "\n";
	            }

	            std::set<Value*> loopInputs;

	            while (!workList.empty()) {
	                GraphNode* n = *workList.begin();
	                workList.erase(n);
	                visitedNodes.insert(n);

	                std::map<GraphNode*, edgeType> preds = n->getPredecessors();

	                for (std::map<GraphNode*, edgeType>::iterator pred = preds.begin(), s_end =
	                     preds.end(); pred != s_end; pred++) {

	                    Value* value = NULL;
	                    if (OpNode* opNode = dyn_cast<OpNode>(pred->first)) {
	                        value = opNode->getValue();
	                    } else {
	                        VarNode* varNode = dyn_cast<VarNode>(pred->first);
	                        value = varNode->getValue();
	                    }

	                    if (dyn_cast<Constant>(value) || visitedNodes.count(pred->first) != 0)
	                        continue;

	                    if (L->isLoopInvariant(value)) {
	                        loopInputs.insert(value);
	                    } else {
	                        workList.insert(pred->first);
	                    }
	                }
	            }

	            return loopInputs;
	        }

	        //Get the list of values that control the loop exit
	        std::set<Value*> getLoopExitPredicates(Loop* L) {
	            std::set<Value*> loopExitPredicates;

	            SmallVector<BasicBlock*, 4> loopExitingBlocks;
	            L->getExitingBlocks(loopExitingBlocks);

	            for (SmallVectorImpl<BasicBlock*>::iterator BB = loopExitingBlocks.begin(); BB != loopExitingBlocks.end(); BB++){
	                if (BranchInst* BI = dyn_cast<BranchInst>((*BB)->getTerminator())) {
	                    loopExitPredicates.insert(BI->getCondition());
	                } else if (SwitchInst* SI = dyn_cast<SwitchInst>((*BB)->getTerminator())) {
	                    loopExitPredicates.insert(SI->getCondition());
	                } else if (IndirectBrInst* IBI = dyn_cast<IndirectBrInst>((*BB)->getTerminator())) {
	                    loopExitPredicates.insert(IBI->getAddress());
	                } else if (InvokeInst* II = dyn_cast<InvokeInst>((*BB)->getTerminator())) {
	                    loopExitPredicates.insert(II);
	                }
	            }

	            return loopExitPredicates;
	        }


	Instruction* findTerminator(Function *F)
	{	for(Function::iterator block=F->begin(), blockend=F->end(); block!=blockend; ++block)
    	{	for(BasicBlock::iterator inst=block->begin(), instend=block->end(); inst!=instend; ++inst)
    		{	if(inst->isTerminator() && inst->getNumOperands()==1)
    				return(inst);

    		}
    	}
		return (NULL);
	}

	virtual bool doInitialization(Function &F)
	{//Initialize pass' persistent variables
		loopcounter=0;
		return true;
	}

	void loopcounterEval(LoopInfoEx& li)
	{//Count the number of loops inside this function and stores in loopinfoit. If loopcounter>loopinfoit,
	 //we have already evaluated all the loops inside the copies of a function foo and should begin analyzing
	 //the copies of a function fou. Therefore we reset the loopcounter.
		int LoopInfoIt=-1; //li.end() = last loop + 1
		loopcounter++;
		for (LoopInfoEx::iterator lit = li.begin(), lend = li.end(); lit != lend; lit++, LoopInfoIt++);

		errs() << "bugpoint " << LoopInfoIt << "<" << loopcounter<<"?\n";
		if(loopcounter>LoopInfoIt)
			loopcounter=0;
	}

	void genDepGraph(Function *F)
	{//This function is strongly based on the runOnFunction function in the LoopControlesDepGraph
	 //pass, made by Raphael Ernani. For further reference search for DepGraph in the ccnuma page
	 //https://code.google.com/p/selective-page-migration-ccnuma/

	//Step 1: Get the complete dependence graph
		functionDepGraph& DepGraph = getAnalysis<functionDepGraph>();
		depGraph = DepGraph.depGraph;

	//Step 2: Get the list of values that control the loop exit
	    LoopInfoEx& li = getAnalysis<LoopInfoEx>();
	    int LoopInfoIt=0;
	    std::set<Value*> loopExitPredicates;

	//Search for a specific loop inside the function
	    LoopInfoIt=0;
	    SmallVector<BasicBlock*, 4> loopExitingBlocks;
	    for (LoopInfoEx::iterator lit = li.begin(); loopcounter>=LoopInfoIt; lit++, LoopInfoIt++)
	    {	loopExitingBlocks.clear();
	    	Loop *l = *lit;
	    	l->getExitingBlocks(loopExitingBlocks);
	    	bool notPresent=true;
	    	for(int i=0; i<loopExitingBlocks.size(); i++)
	    		if(loopExitingBlocks[i]==l->getHeader())
	    			notPresent=false;


	    	if(notPresent)
	    		loopExitingBlocks.push_back(l->getHeader());
	    }


	    for(SmallVectorImpl<BasicBlock*>::iterator BB = loopExitingBlocks.begin(); BB != loopExitingBlocks.end(); BB++){
			if (BranchInst* BI = dyn_cast<BranchInst>((*BB)->getTerminator())) {
				loopExitPredicates.insert(BI->getCondition());
			} else if (SwitchInst* SI = dyn_cast<SwitchInst>((*BB)->getTerminator())) {
				loopExitPredicates.insert(SI->getCondition());
			} else if (IndirectBrInst* IBI = dyn_cast<IndirectBrInst>((*BB)->getTerminator())) {
				loopExitPredicates.insert(IBI->getAddress());
			} else if (InvokeInst* II = dyn_cast<InvokeInst>((*BB)->getTerminator())) {
				loopExitPredicates.insert(II);
			}
		}

	//Step 3: Make a list of graph nodes that represent the dependencies of the loop controllers
	    std::set<GraphNode*> visitedNodes;
	    for(std::set<Value*>::iterator v = loopExitPredicates.begin(); v != loopExitPredicates.end(); v++){
	    	if (GraphNode* valueNode = depGraph->findNode(*v))
	    		depGraph->dfsVisitBack(valueNode, visitedNodes);
	    	else
	    		errs() << "Function : " << F->getName() << " - Value not found in the graph : " << **v << "\n";
	    }

	//Step 4: Remove from the graph all the nodes that are not in the list of dependencies
	    std::set<GraphNode*> nodesToRemove;
	    for(Graph::iterator node = depGraph->begin(); node != depGraph->end(); node++ )
	    	if (!visitedNodes.count(*node)) nodesToRemove.insert(*node);

		for(std::set<GraphNode*>::iterator node = nodesToRemove.begin(); node != nodesToRemove.end(); node++ )
		   	depGraph->removeNode(*node);

	//Step 5: ta-da! The graph is ready to use :)
	    fullGraph = depGraph;
	}

	void setAnalyzedBranch(Function *F)
	{
		LoopInfoEx& li = getAnalysis<LoopInfoEx>();

		int LoopInfoIt=1;

		//Get the analyzed loop
		LoopInfoEx::iterator analyzedIt=li.begin();
		for (LoopInfoEx::iterator lit = li.begin(); loopcounter>=LoopInfoIt; analyzedIt++, LoopInfoIt++);

		Loop *AnalyzedLoop = *analyzedIt;
		LoopInfoEx::iterator auxIt=analyzedIt;

		//Get the outtermost loop containing analyzed loop
		for(LoopInfoEx::iterator lit=li.begin(), lend=li.end(); lit!=lend; lit++)
		{
			Loop *l=*lit;
			Loop *auxLoop=*auxIt;

			if(l->contains(auxLoop) && lit!=auxIt)
			{	auxIt=lit;
				lit=li.begin();
			}
		}

		Loop *OuttermostLoop = *auxIt;

		//Get the branch instruction of each header
		BasicBlock *OutterHeader=OuttermostLoop->getHeader();
		BasicBlock::iterator outterBr=OutterHeader->begin();

		for(BasicBlock::iterator instEnd=OutterHeader->end(); outterBr!=instEnd; outterBr++)
			if(outterBr->isTerminator())
				break;

		BasicBlock *AnalyzedHeader=AnalyzedLoop->getHeader();
		BasicBlock::iterator analyzedBr=AnalyzedHeader->begin();

		for(BasicBlock::iterator instEnd=AnalyzedHeader->end(); analyzedBr!=instEnd; analyzedBr++)
			if(analyzedBr->isTerminator())
				break;

		string st2, st3;
		llvm:raw_string_ostream rs_old(st2), rs_outter(st3);
		analyzedBr->print(rs_old);
		outterBr->print(rs_outter);

		Instruction *oldInst = analyzedBr;
		Instruction *newInst = oldInst->clone();
		Instruction *useInst = outterBr;

		newInst->setOperand(1,useInst->getOperand(1));

		string st1;
		llvm::raw_string_ostream rso_newbr(st1);

		newInst->insertAfter(oldInst);
		oldInst->dropAllReferences();
		oldInst->removeFromParent();
		newInst->print(rso_newbr);

		errs() << "AnalyzedBranch_use: " << rs_outter.str() << "\n"; //A new terminator was created.
		errs() << "AnalyzedBranch_old: " << rs_old.str() << "\n"; //A new terminator was created.
		errs() << "AnalyzedBranch_new: " << rso_newbr.str() << "\n"; //A new terminator was created.

		}


	bool loopSlice(Function *F)
	{//Runs on each function removing instructions not related to the loop

		errs() << "Iteration " << loopcounter << " " << F->getName() << "\n\n";
		string s=F->getName();
		string prefix="loopExtractionFun_";
	//Only look at functions created for the loopExtraction
		if(s.compare(0,prefix.size(),prefix)!=0)
			return (false);

	//Generate a Dependence Graph for the given function
		genDepGraph(F);
		LoopInfoEx& li = getAnalysis<LoopInfoEx>();
		bool changed=false;

	//Step6: Iterate through instructions and remove those that have no depedencies associated with the
	//loop controler variables

	//Create a vector containing the Function's BasicBlocks. With this we can iterate trough the bb
	//In reverse order, therefore avoiding removing a definition before it's use.

		setAnalyzedBranch(F);

		vector<BasicBlock*> Fun;
	    for(Function::iterator block=F->begin(), BBend=F->end(); block!=BBend; ++block)
	    	Fun.push_back(block);

	    for(int i=Fun.size()-1; i>=0; i--)
	    {	BasicBlock *BB = Fun[i];
	    	if(!BB)
	    		return false;
	//Create a vector containing the BasicBlock's instruction. Same purpose explained above.
	    	vector<Instruction*> basicBlock;
	    	for(BasicBlock::iterator ins=BB->begin(), finst=BB->end(); ins!=finst; ++ins)
	    		basicBlock.push_back(ins);

	    	for(int j=basicBlock.size()-1; j>=0; j--)
	    	{	bool InstHasOperand=false;
	    		Instruction *inst=basicBlock[j];
	    		std::string str;
	    		llvm::raw_string_ostream rso(str);
	    		inst->print(rso);
	//If the first operand is present in our DepGraph, this instruction most likely change
	//one of the variables used to control the loop exit and, therefore, should remain.
	    		Instruction::op_iterator Op = inst->op_begin();

	    		if(PHINode *PN = dyn_cast<PHINode>(inst))
	    		{	if(fullGraph->findNode(inst))
	    				InstHasOperand=true;
	    		}
	    		else if (AllocaInst *AI = dyn_cast<AllocaInst>(inst))
	    		{	if(fullGraph->findNode(inst))
    					InstHasOperand=true;
	    		}
	    		else if (StoreInst *SI = dyn_cast<StoreInst>(inst))
	    		{	if(fullGraph->findNode(inst->getOperand(1)))
	    				InstHasOperand=true;
	    		}
				else if (BinaryOperator *BO = dyn_cast<BinaryOperator>(inst))
				{	if(fullGraph->findNode(inst))
						InstHasOperand=true;
				}
				else if (CmpInst *CmI = dyn_cast<CmpInst>(inst))
				{	if(fullGraph->findNode(inst))
						InstHasOperand=true;
				}
	    		else if (CallInst *CI = dyn_cast<CallInst>(inst))
				{	if(fullGraph->findNode(inst))
						InstHasOperand=true;
				}
	    		else if(fullGraph->findNode(Op->get()))
	    			InstHasOperand=true;

	//If it's a 'useless' instruction
	    		if(InstHasOperand==false){
	//If is the terminator of a BB
	    				if(inst->isTerminator()){
	//If it has more that one operand, that this instruction involves some kind of comparassion (f.e. slt)
	//and a branch if true and if false. However, if we arrived this far we know that this instruction has
	//nothing to do with the loop being analized and therefore we will make is a simple branch instruction.
	    				if(inst->getNumOperands()>1)
	    				{
	    					std::string str1;
	    					llvm::raw_string_ostream rso1(str1);

	 //DONE: Check if the loop being analysed is inside the loop in which 'inst' is
	 //		 contained. If true: getOperand(0); else: getOperand(1);
	 //DONE: Change de ifFalse of the analysed branch to the ifFalse of the outter
	 //		 most branch.


	    					int LoopInfoIt=1;

	    					//Search for the analyzed loop
	    					LoopInfoEx::iterator analyzedIt=li.begin(), instLoopIt=li.begin();
	    					for (LoopInfoEx::iterator lit = li.begin(); loopcounter>=LoopInfoIt; analyzedIt++, LoopInfoIt++);

	    					Loop *AnalyzedLoop = *analyzedIt;
	    					//errs() << "\t" << AnalyzedLoop->getHeader()->getName();

	    				    //Search for the loop containing inst
	    					for(; instLoopIt!=li.end();instLoopIt++)
	    					{	Loop *l=*instLoopIt;
	    						if(l->contains(inst))
	    							break;
	    					}


	    					Loop *InstLoop= *instLoopIt;
	    					//errs() << " " << InstLoop->getHeader()->getName();

	    	//Find a model instruction "br label %whatever"
	    					Instruction* newInst=findTerminator(F)->clone();

	    					if(InstLoop->contains(AnalyzedLoop))
	    						newInst->setOperand(0,inst->getOperand(2));
	    					else
	    						newInst->setOperand(0,inst->getOperand(1));


	//Adjust %whatever to the if(false) operand of the original terminator
	    					//newInst->setOperand(0,v);
	    					newInst->insertAfter(inst);
	    					inst->dropAllReferences();
	    					inst->removeFromParent();
	    					newInst->print(rso1);
	    					errs() << "NBranch: " << rso1.str() << "\n"; //A new terminator was created.
	    					changed=true;
	    				}
	    				else errs() << "Preserv: " << rso.str() << "\n";//The original terminator was preserved.
	    			}
	    			else
	    			{	errs() << "Removed: " << rso.str() << "\n";//The original instruction was removed.
	    				inst->dropAllReferences();
	    				inst->removeFromParent();
	    				changed=true;
	    			}
	    		}
	    		else
	    		{	LoopInfoEx::iterator analyzedIt=li.begin(), instLoopIt=li.begin();
	    			int LoopInfoIt=1;
					for (LoopInfoEx::iterator lit = li.begin(); loopcounter>=LoopInfoIt; analyzedIt++, LoopInfoIt++);

					Loop *AnalyzedLoop = *analyzedIt;

	    			if(!AnalyzedLoop->contains(inst) && !inst->isTerminator())
	    			{	errs() << "Removed: " << rso.str() << "\n";//The original instruction was removed.
	    				inst->dropAllReferences();
    					inst->removeFromParent();
    					changed=true;
	    			}
	    			else
	    				errs() << "Preserv: " << rso.str() << "\n";//The original instruction was preserved.
	    		}

	    	}
	    	basicBlock.clear(); //Release the memory used by our vector of instructions
	    }
	    Fun.clear(); 	//Release the memory used by our vector of basicblock
	    loopcounterEval(li); 	//Set loopcounter to evalute the next loop inside our original function
	    return changed;	//If any change was made, return true.
		}//End function


	Function* removeReturnInst(Function* F) {

	      // Collect them all first, as we can't remove them while iterating.
	      // While iterating, we can add the new retvals (ret void).
	      SmallPtrSet<ReturnInst*, 4> rets;
	      for (inst_iterator I = inst_begin(F), E = inst_end(F); I != E; ++I) {

	        if (!I->isTerminator())
	          continue; // ignore non terminals

	        if (ReturnInst* retInst = dyn_cast<ReturnInst>(&*I)) {

	          // Create the return void instruction
	          ReturnInst::Create(F->getContext(), 0, retInst);

	          // Save return value instruction for removal
	          rets.insert(retInst);
	        }
	      }

	      // Now, remove all return values
	      for (SmallPtrSet<ReturnInst*, 4>::iterator i = rets.begin(),
	           ie = rets.end(); i != ie; ++i) {
	        (*i)->eraseFromParent();
	      }

	      return F;
	    }




	virtual bool runOnFunction(Function &F)
	{
		string s=F.getName();
		string prefix="loopExtractionFun_";
		//Only look at functions created for the loopExtraction
		if(!(s.compare(0,prefix.size(),prefix)==0))
			return (false);

		string trashPrefix = "loopExtractionTrash";
		if(s.compare(0,trashPrefix.size(),prefix)==0)
			return(false);

		LoopInfoEx &LI = getAnalysis<LoopInfoEx>();
		int timesToClone=0;
		bool changed;

		for (LoopInfoEx::iterator i = LI.begin(), e = LI.end(); i != e; i++, timesToClone++);



			Function *OF=&F;

			//Get the analyzed loop
			LoopInfoEx::iterator analyzedIt=LI.begin(), instLoopIt=LI.begin();
			int LoopInfoIt=0;
			for (; loopcounter>LoopInfoIt; analyzedIt++, LoopInfoIt++);

			Loop *AnalyzedLoop = *analyzedIt;
			genDepGraph(OF);

			set<Value*> loopinputs = getLoopInputs(AnalyzedLoop, depGraph);

			for(set<Value*>::iterator it=loopinputs.begin(); it!=loopinputs.end(); it++)
			{	Value *val = *it;
				errs() << "val " + val->getName() + "\n";

			}

			FunctionType* useFT = OF->getFunctionType();

			std::vector<Type*> params;

			vector<string> newArgsNames;

			for(Function::arg_iterator argit = OF->arg_begin(); argit!=OF->arg_end(); argit++)
			{
				newArgsNames.push_back(argit->getName());
				params.push_back(argit->getType());
			}

			for (set<Value*>::iterator it = loopinputs.begin(); it!=loopinputs.end(); it++) {
				Value *val = *it;

				unsigned int i=0;
				for(; i<newArgsNames.size(); i++)
				{	if(newArgsNames[i]==val->getName())
						break;
				}
				if(i==newArgsNames.size()) //Didnt find
				{	params.push_back(val->getType());
					newArgsNames.push_back(val->getName());
				}
			}

			FunctionType *NewFnType = FunctionType::get(OF->getReturnType(), params, OF->isVarArg());
			Function *NewF = Function::Create(NewFnType, OF->getLinkage());
			NewF->copyAttributesFrom(OF);
			OF->getParent()->getFunctionList().push_front(NewF);

			Function::arg_iterator NFArg = NewF->arg_begin();
			for (unsigned int i=0; i<newArgsNames.size(); i++, NFArg++) {

			      NFArg->setName(newArgsNames[i]);
			      errs() << "arg: " + NFArg->getName() + "\n";
			    }

			NewF->getBasicBlockList().splice(NewF->begin(), OF->getBasicBlockList());

			// Replace all uses of the old arguments with the new arguments
			for (llvm::Function::arg_iterator I = OF->arg_begin(), E = OF->arg_end(),
			           NI = NewF->arg_begin(); I != E; ++I, ++NI)
			      I->replaceAllUsesWith(NI);

			string fname = OF->getName();
			OF->setName("loopExtractionTrash");
			NewF->setName(fname);

			for(set<Value*>::iterator it=loopinputs.begin(); it!=loopinputs.end(); it++)
			{	Value *val = *it;
				string valName = val->getName();
				errs() << "val " + val->getName() + "\n";
				for (llvm::Function::arg_iterator I = NewF->arg_begin(), E = NewF->arg_end()
						; I != E; ++I){
					string argName = I->getName();

					if(valName.compare(argName)==1)
					{	if(valName[argName.size()]=='1')
						{	errs() << "Replacing use of " + valName + " for " + argName + "\n";
							val->replaceAllUsesWith(I);
						}
					}
				}

			}

			changed = loopSlice(NewF);
			errs() << "sliced";


		return changed;
	}

    };//End struct
}//End namespace

char FunLoopSlicing::ID=1;

static RegisterPass<FunLoopSlicing> Z("FunLoopSlicing", "Slice the loops inside each function",
                             false /* looks at CFG */,
                             true /* Transform Pass */);
