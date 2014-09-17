#include "LoopInstrumentation.h"

#include "llvm/IR/IRBuilder.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/CFG.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"

LoopInstrumentation::LoopInstrumentation() : FunctionPass(ID) {
    this->printf = NULL;
}

void LoopInstrumentation::getAnalysisUsage(AnalysisUsage &AU) const{
    AU.addRequired<functionDepGraph> ();
    AU.addRequiredTransitive<LoopInfoEx> ();
}

bool LoopInstrumentation::runOnFunction(Function &F) {
    LLVMContext& ctx = F.getParent()->getContext();
    
    //Get the complete dependence graph
    functionDepGraph& DepGraph = getAnalysis<functionDepGraph> ();
    Graph* depGraph = DepGraph.depGraph;
    
    LoopInfoEx& li = getAnalysis<LoopInfoEx>();
    
    int counter = 0;
    for (LoopInfoEx::iterator lit = li.begin(), lend = li.end(); lit != lend; lit++) {
        Loop* l = *lit;
        
        BasicBlock *loopHeader = l->getHeader();
        
        //Get or create a loop preheader
        BasicBlock *preHeader;
        
        if (BasicBlock *block = l->getLoopPreheader()) {
            preHeader = block;
        } else {
            std::vector<BasicBlock*> preHeaders;
            for (pred_iterator PI = pred_begin(loopHeader); PI != pred_end(loopHeader); ++PI) {
                BasicBlock *pred = *PI;
                if (!l->contains(pred)) {
                    preHeaders.push_back(pred);
                }
            }
            
            preHeader = SplitBlockPredecessors(loopHeader, ArrayRef<BasicBlock*>(preHeaders), "preHeader");
        }
        
        Instruction *lastInst = preHeader->getTerminator();
        
        //Get the loop exit predicates
        std::set<Value*> loopInputs = getLoopInputs(l, depGraph);
        
        //Insert printf calls
        for (std::set<Value*>::iterator it = loopInputs.begin(); it != loopInputs.end(); it++) {
            createPrintfCall(F.getParent(), lastInst, *it);
        }
        
        //Create trip counter
        Twine varName = F.getName() + Twine(".loopCounter.") + Twine(counter++);
        Value *counter = createCounter(l, varName, ctx);
        
        SmallVector<BasicBlock*, 4> exitBlocks;
        l->getExitBlocks(exitBlocks);
        for (SmallVectorImpl<BasicBlock*>::iterator it = exitBlocks.begin(); it != exitBlocks.end(); it++) {
            BasicBlock *exBB = *it;
            createPrintfCall(F.getParent(), exBB->getFirstInsertionPt(), counter);
        }
    }
    return false;
}

//Fix point algoritm to get the variables defined outside the loop
set<Value*> LoopInstrumentation::getLoopInputs(Loop *L, Graph *depGraph) {
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
            } else if (VarNode* varNode = dyn_cast<VarNode>(pred->first)) {
                value = varNode->getValue();
            } else {
                continue;
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
std::set<Value*> LoopInstrumentation::getLoopExitPredicates(Loop* L) {
    std::set<Value*> loopExitPredicates;
    
    SmallVector<BasicBlock*, 4> loopExitingBlocks;
    L->getExitingBlocks(loopExitingBlocks);
    
    for (SmallVectorImpl<BasicBlock*>::iterator BB = loopExitingBlocks.begin(); BB != loopExitingBlocks.end(); BB++){
        if (BranchInst* BI = dyn_cast<BranchInst>((*BB)->getTerminator())) {
            if (!BI->isConditional()) continue;
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

Value *LoopInstrumentation::createCounter(Loop *L, Twine varName, LLVMContext& ctx) {
    BasicBlock *loopHeader = L->getHeader();
    IRBuilder<> builder(loopHeader->getFirstNonPHI());
    
    int nPreds = std::distance(pred_begin(loopHeader), pred_end(loopHeader));
    PHINode *counter = builder.CreatePHI(Type::getInt32Ty(ctx), nPreds, varName);
    
    //Get the loopHeader successor inside the loop
    /*BasicBlock *succ = NULL;
    if (L->contains(loopHeader->getTerminator()->getSuccessor(0))) {
        succ = loopHeader->getTerminator()->getSuccessor(0);
    } else {
        succ = loopHeader->getTerminator()->getSuccessor(1);
    }
    builder.SetInsertPoint(succ->getFirstInsertionPt());*/
    builder.SetInsertPoint(loopHeader->getFirstInsertionPt());
    Value *inc = builder.CreateAdd(counter, ConstantInt::get(Type::getInt32Ty(ctx), 1));
    
    //Add PHINode incomings
    for (pred_iterator PI = pred_begin(loopHeader); PI != pred_end(loopHeader); ++PI) {
        BasicBlock *pred = *PI;
        if (L->contains(pred)) {
            counter->addIncoming(inc, pred);
        } else {
            counter->addIncoming(ConstantInt::get(Type::getInt32Ty(ctx), 0), pred);
        }
    }
    return counter;
}

CallInst *LoopInstrumentation::createPrintfCall(Module *module, Instruction *insertPoint, Value *param) {
    LLVMContext& ctx = module->getContext();
    IRBuilder<> builder(ctx);
    builder.SetInsertPoint(insertPoint);
    
    Constant *zero = Constant::getNullValue(IntegerType::getInt32Ty(ctx));
    
    std::vector<llvm::Constant*> indices;
    indices.push_back(zero);
    indices.push_back(zero);
    Constant *var_ref = ConstantExpr::getGetElementPtr(getFormat(module), indices);
    
    GlobalVariable *varName = getConstString(module, param->getName(), param->getName().str());
    Constant *varName_ref = ConstantExpr::getGetElementPtr(varName, indices);
    
    CallInst *call = builder.CreateCall3(getPrintf(module), var_ref, varName_ref, param, "printf");
    
    return call;
}

Function *LoopInstrumentation::getPrintf(Module *module) {
    if (!this->printf) {
        LLVMContext& ctx = module->getContext();
        std::vector<Type*> argTypes;
        argTypes.push_back(Type::getInt8PtrTy(ctx));
        FunctionType *MTy = FunctionType::get(Type::getInt32Ty(ctx), argTypes, true);
        
        Constant *funcConst = module->getOrInsertFunction("printf", MTy);
        this->printf = cast<Function>(funcConst);
    }
    return this->printf;
}

char LoopInstrumentation::ID = 0;
static RegisterPass<LoopInstrumentation> X("instr-loop", "Instrument the loops of a function to print the loop exit predicates.");