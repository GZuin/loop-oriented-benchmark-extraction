#include <string>
#include <fstream>
#include <vector>
#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instruction.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Support/CallSite.h"



using namespace llvm;
using namespace std;

namespace {
  struct BytecodeTranslator : public FunctionPass {
	static char ID;
    BytecodeTranslator() : FunctionPass(ID) {}



    unsigned int findValue(Value* v, vector<Value*> tempVariables)
    {//Try to find value inside our vector. If it's not there, then add it
    	unsigned int i;
    	for(i=0; i<tempVariables.size(); i++)
    	{	if(tempVariables[i]==v)
    			return(i);
    	}
    	tempVariables.push_back(v);
    	return(i);
    }

	string fileId()
	{//Generates a random 6 characters string to differentiate beetween files with the same name
		string fileId="benchmarks/benchmark_";

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

			//fileId+=(randomChar);
		}
		return (fileId); //Ex.: "_F74t0"
	}

	string intToStr(unsigned int i)
	{	string strInt="";
		while(i>0)
		{	int aux=i%10;
			i=i/10;
			char c=aux+48;
			strInt+=c;
		}

		return(strInt);
	}

	string simpleInstType (Type *Ty)
	{
		switch (Ty->getTypeID()) {

		case Type::VoidTyID: return "void";

		case Type::IntegerTyID: {
	    	int numBits = cast<IntegerType>(Ty)->getBitWidth();
		    if(numBits==1)
		    	return "bool";
		    else if(numBits<=8)
		    	return "char";
		    else if (numBits<=32)
		    	return "int";
		    else if(numBits<=64)
		    	return "long long";}
		break;
	  case Type::FloatTyID: return "float";
	  case Type::DoubleTyID: return "double";
	  default: return "void";
	  }
	}


    virtual bool runOnFunction(Function &F)
    {	string s=F.getName();
		string prefix="loopExtractionFun_";
		//Only look at functions created for the loopExtraction
		if(s.compare(0,prefix.size(),prefix)!=0)
			return (false);

		string filename = fileId();
		ofstream outp;
		outp.open(filename.c_str(), ofstream::out);
		outp << "int main(int argc, char *argv[])\n{\n";
		vector<Value*> tempVariables;

		for(Function::iterator bb=F.begin(), be=F.end();bb!=be;++bb)
		{	std::string str;
			llvm::raw_string_ostream rso_bb(str);
			rso_bb<<bb->getName();
			outp<<rso_bb.str()<<":\n";
			for(BasicBlock::iterator inst=bb->begin(), ie=bb->end(); inst!=ie; ++inst)
			{
				std::string str1;
				llvm::raw_string_ostream rso_inst(str1);

				if (ReturnInst* RI = dyn_cast<ReturnInst>(inst))
				{
					outp<<"return (0);\t";
				}
				else if (BranchInst* BI = dyn_cast<BranchInst>(inst))
				{	if(inst->getNumOperands()==1)
					{	rso_inst<<BI->getSuccessor(0)->getName();
						outp<<"goto "<<rso_inst.str()<<";\t";
					}
					else
					{
						string name=BI->getCondition()->getName();
						if(name.empty())
							name="tmp_" + intToStr(findValue(BI->getCondition(),tempVariables));

						rso_inst<<BI->getSuccessor(0)->getName();
						std::string str2;
						llvm::raw_string_ostream rso_inst2(str2);
						rso_inst2<<BI->getSuccessor(1)->getName();

						outp<<"if("<<name<<"){\n\tgoto " << rso_inst.str() << ";\n}\nelse{\n\tgoto " << rso_inst2.str()<<";\t}";

					}
				}
				else if (AllocaInst* AI = dyn_cast<AllocaInst>(inst))
				{	//AllocaInst *AI;
					outp<<simpleInstType(AI->getType()->getElementType()) <<" ";

					string aux=AI->getName();
					for(int i=0; i<aux.size(); i++)
						if (aux[i]=='.') aux[i]='_';


					outp << aux << ";\t";
					/*string str0, str1;
					raw_string_ostream rso0(str0), rso1(str1);

					rso0<<AI->getOperand(1)->getName();
					rso1<<AI->getOperand(0)->getName();

					string op0=rso0.str();
					string op1=rso1.str();

					if(op0.empty())
						op0 = "tmp_" + intToStr(findValue(AI->getOperand(1),tempVariables));
					if(op1.empty())
						op1 = "tmp_" + intToStr(findValue(AI->getOperand(0),tempVariables));

					inst->print(rso_inst);

					outp<< " = " << op1 << "   " << rso_inst.str()<<"\n";
					*/

				}


				inst->print(rso_inst);
				outp<< "\\\\" << rso_inst.str() << "\n";
			}
		}

		outp<<"}";
		outp.close();
		return (false);
    }
  };
}

char BytecodeTranslator::ID = 0;
static RegisterPass<BytecodeTranslator> X("BytecodeTranslator", "Backend translator from BC to C", false, false);
