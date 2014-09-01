//
//  LoopInstrumentation.h
//
//
//  Created by Demontiê Junior on 9/1/14.
//
//

#ifndef _LoopInstrumentation_h
#define _LoopInstrumentation_h

#include <vector>

#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Constants.h"
#include "llvm/Pass.h"

#include "DepGraph.h"

using namespace llvm;


class LoopInstrumentation : public FunctionPass {
public:
    static char ID; // Pass identification, replacement for typeid
    
    LoopInstrumentation();
    
    void getAnalysisUsage(AnalysisUsage &AU) const;
    
    virtual bool runOnFunction(Function &F);
    
private:
    Function *printf;
    
    //Fix point algoritm to get the variables defined outside the loop
    set<Value*> getLoopInputs(Loop *L, Graph *depGraph);
    
    //Get the list of values that control the loop exit
    std::set<Value*> getLoopExitPredicates(Loop* L);
    
    Value *createCounter(Loop *L, Twine varName, LLVMContext& ctx);
    
    CallInst *createPrintfCall(Module *module, Instruction *insertPoint, Value *param);
    
    Function *getPrintf(Module *module);
    
    static GlobalVariable *getFormat(Module *module) {
        return getConstString(module, StringRef("format"), StringRef("%s = %d\n"));
    }
    
    static GlobalVariable *getConstString(Module *module, StringRef name, StringRef str) {
        Twine gvName = Twine(name) + Twine(".str");
        if (GlobalVariable *gv = module->getNamedGlobal(gvName.str()))
            return gv;
        
        LLVMContext& ctx = module->getContext();
        Constant *format_const = ConstantDataArray::getString(ctx, str.str());
        GlobalVariable *var
            = new GlobalVariable(*module, ArrayType::get(IntegerType::get(ctx, 8), str.size()+1),
                                 true, GlobalValue::PrivateLinkage, format_const, gvName);
        return var;
    }
    
};

#endif
