#include <string>
#include <iostream>
#include <fstream>
#include <vector>
#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instruction.h"
#include "llvm/Analysis/LoopPass.h"				//LoopBase info
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Module.h"						//Module info
#include "llvm/IR/Instructions.h"
#include "llvm/Support/CallSite.h"
#include "llvm/Support/GetElementPtrTypeIterator.h"
#include <map>

//TODO: Quando uma variavel recebe argc ou argv[] ou uma variavel global, esta imprimindo
//		algo do tipo b = ;



using namespace llvm;
using namespace std;

namespace {
  struct BytecodeTranslator : public ModulePass {
	static char ID;
    BytecodeTranslator() : ModulePass(ID) {}

    void getAnalysisUsage(AnalysisUsage &AU) const {
        	                        AU.addRequired<LoopInfo>();
        	                        AU.addPreserved<LoopInfo>();
        	                }

    unsigned int findValue(string v, vector<string> vet)
    {//Try to find value inside our vector. If it's not there, then add it
    	unsigned int i;
    	for(i=0; i<vet.size(); i++)
    	{	if(vet[i]==v)
    			return(i);
    	}
    	vet.push_back(v);
    	return(-1);
    }

	string fileId()
	{//Generates a random 6 characters string to differentiate beetween files with the same name
		string fileId="benchmarks/benchmark_";

		//Generate random seed
		srand(random());
		int i;

		//Fill fileId
		for(i=1; i<=7; ++i)
		{	//In the ASC table, numbers+letters go from 48 to 122
			char randomChar=rand()%72+48;

			//if char is :?@ etc
			if((randomChar>=58 && randomChar<=64) || (randomChar>=91 && randomChar<=96))
				randomChar+=7;

			fileId+=(randomChar);

		}
		fileId+=".cpp";
		return (fileId); //Ex.: "_F74t0"
	}

	string intToStr(unsigned int i)
	{//Converts an integer to a string
		if(i==0)
				return("0");

		string strInt="";

		while(i>0)
		{	int aux=i%10;
			i=i/10;
			char c=aux+48;
			strInt+=c;
		}

		return(strInt);
	}

	bool shouldRemoveStruct(Function *F, StructType* sty)
	{	bool ret = true;
		for(Function::iterator inst = F->begin(); inst!=F->end(); inst++)
		{	if (GetElementPtrInst* PI = dyn_cast<GetElementPtrInst>(inst))
			{	StructType *styIt = dyn_cast<StructType>(PI->getPointerOperand()->getType()->getPointerElementType());
				if(styIt == sty)
				{	ret=false;
					break;
				}
			}

		}
		return(ret);
	}

	string simpleInstType (Type *Ty)
	{//Returns the type of a instruction
		switch (Ty->getTypeID()) {

		case Type::VoidTyID: return "void";
		case Type::ArrayTyID: return(simpleInstType(Ty->getPointerElementType())+"[]");
		case Type::PointerTyID: return(simpleInstType(Ty->getPointerElementType())+"*");
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
	  default: return "void*";
	  }
	}

	string globalVarType (Type *Ty)
		{//Returns the type of a instruction
		return(simpleInstType(Ty->getPointerElementType()));
		}


    virtual bool runOnModule(Module &M)
    {//Run on module pass
    	//Map containing the programs registers and the variables they're associated to.
    	map<string,string> registerTable;
    	srand(time(NULL));
    	string globalVariables="\n//Global Variables\n";
    	vector<string> globalStructs;
    	globalStructs.push_back("\n//Global Structures\n");

    	for(Module::global_iterator gv=M.global_begin(); gv!=M.global_end(); ++gv)
    	{	string auxgv;
    		raw_string_ostream rsgv(auxgv);
    		rsgv<<gv->getName();
    		string gvTy = globalVarType(gv->getType());

    		globalVariables+=gvTy + " " + rsgv.str()+" = ";

    		auxgv.clear();
    		rsgv.flush();

    		string gvinit;
    		raw_string_ostream rsinit(gvinit);

    		gv->getInitializer()->print(rsinit);
    		gvinit = rsinit.str();
    		while(gvinit[0]!=' ') gvinit.erase(0,1);
    		gvinit.erase(0,1);

    		if(gvinit=="null") gvinit="NULL";

    		globalVariables+=gvinit+";\n";

    	}

    	for (Module::iterator Foo=M.begin(), FooE=M.end(); Foo!=FooE; ++Foo)
		{//Run on each function
    		string s=Foo->getName();
			string prefix="loopExtractionFun_";

			//if(s.compare(0,prefix.size(),prefix)!=0)
			//	continue;

			//Get loop analysis
			LoopInfo &Loops = getAnalysis<LoopInfo>(*Foo);

			//Open a new file for the benchmark
			string filename = fileId();
			string funStr, funDStr;
			raw_string_ostream funBody(funStr), funDeclarations(funDStr);

			funDeclarations<<"//Function Declarations\n";

			string header="#include <cstdio>\n#include <cstdlib>\n#include \"argvHandler.h\"\n\n";

			ofstream outp;
			outp.open(filename.c_str(), ofstream::out);

			vector<Function*> shouldPrintFun;
			shouldPrintFun.push_back(Foo);

			for(int fun=0; fun!=shouldPrintFun.size();fun++)
			{	Function *F=shouldPrintFun[fun];

				//Maps containing each BB translated instructions and the goto of each one
				map<BasicBlock*,string> fileOutMap;
				map<BasicBlock*,string> fileBROutMap;

				//Vector containing the function's arguments
				vector<string> arguments;
				//Vector containing the variables already defined on the benchmark
				vector<string> definedVars;

				for(Module::global_iterator gv=M.global_begin(); gv!=M.global_end(); ++gv)
				{	string auxgv;
					raw_string_ostream rsgv(auxgv);
					rsgv<<gv->getName();

					definedVars.push_back(rsgv.str());
				}

				vector<string> variableDeclarations;

				//For each of the function's arguments, add them to our vector
				for(Function::arg_iterator ab=F->arg_begin(), ae=F->arg_end(); ab!=ae; ++ab)
					arguments.push_back(ab->getName());

				if(fun==0)	//Default header
				{	funBody <<	"\nint main(int argc, char *argv[])\n{\n";

					if(arguments.size()>0)
						funBody<< "\tif (argc<" + intToStr(arguments.size()+1) +"){\n\t\printf(\"Missing function arguments, presented %d and expected " +  intToStr(arguments.size()) + "\\n\",argc-1);\n\t\treturn(-1);\n\t}\n\n";

				}
				else
				{
					string funTy = simpleInstType(F->getReturnType());
					string funNm;
					raw_string_ostream rsfnm(funNm);

					rsfnm << F->getName();

					//funNm+= "(";

					funBody << funTy + " " + rsfnm.str() + "(";
					funDeclarations << funTy + " " + rsfnm.str() + "(";
					for(Function::arg_iterator ab=F->arg_begin(), ae=F->arg_end(); ab!=ae; ++ab)
					{	string argTy = simpleInstType(ab->getType());
						string argNm;
						raw_string_ostream rsanm(argNm);
						rsanm << ab->getName();
						if(ab!=F->arg_begin())
						{	funBody<< ",";
							funDeclarations<<",";
						}
						funBody<< argTy + " " + rsanm.str();
						funDeclarations <<argTy + " " + rsanm.str();
					}
					funBody<<")\n{\n";
					funDeclarations<<");\n";
				}


				for(Function::iterator bb=F->begin(), be=F->end();bb!=be;++bb)
				{	fileOutMap.insert(pair<BasicBlock*,string>(bb,""));
					fileBROutMap.insert(pair<BasicBlock*,string>(bb,""));
				}
				for(Function::iterator bb=F->begin(), be=F->end();bb!=be;++bb)
				{//For each function's basic block
					string fileOutput="";
					//Get basic block name (used for labels)
					std::string str;
					llvm::raw_string_ostream rso_bb(str);
					rso_bb<<bb->getName();
					string blockName = rso_bb.str();

					//Change '.' to '_'
					for(int i=0; i<blockName.size(); i++)
						if (blockName[i]=='.') blockName[i]='_';

					//If it's not the first block, print bb's name as a label
					if(bb!=F->begin())
						fileOutput+=blockName + ":\n";
					else
					{
						if(fun==0)
							for(Function::arg_iterator ab=F->arg_begin(), ae=F->arg_end(); ab!=ae; ++ab)
							{	string argType = simpleInstType(ab->getType());
								string argName = ab->getName();
								string aux="\t" + argType + " " + argName +  " = getArgvArgument(argv," + intToStr(ab->getArgNo() + 1) + "," + argName + ");\n";
								variableDeclarations.push_back(aux);
								definedVars.push_back(argName);
							}

					}

					//If the bb is a Loop Header
					if(Loops.isLoopHeader(bb) && fun==0)
					{
						//Create a loop counter
						string loopCounter= "loopCounter_";
						for(int i=1; i<=5; ++i)
						{	//In the ASC table, numbers+letters go from 48 to 122
							char randomChar=rand()%72+48;

							//if char is :?@ etc
							if((randomChar>=58 && randomChar<=64) || (randomChar>=91 && randomChar<=96))
								randomChar+=7;
							loopCounter+=(randomChar);
						}
						//Add the loopcounter definition
						string varDef="\tint " + loopCounter + " = 0;\n";
						variableDeclarations.push_back(varDef);
						definedVars.push_back(loopCounter);

						//Add the loopcounter increment
						fileOutput+="\t" + loopCounter + " = " + loopCounter + " + 1;\n";
					}

					for(BasicBlock::iterator inst=bb->begin(), ie=bb->end(); inst!=ie; ++inst)
					{//For each instruction
						std::string str1;
						llvm::raw_string_ostream rso_inst(str1);

						string debugstr;
						raw_string_ostream rsdbg(debugstr);

						inst->print(rsdbg);
						//cout << rsdbg.str() + "\n";

						if (GetElementPtrInst* PI = dyn_cast<GetElementPtrInst>(inst))
						{//GetElementPtrInst* PI;
							if (PI->getPointerOperand()->getType()->getPointerElementType()->isStructTy())
							{
								StructType *sty = dyn_cast<StructType>(PI->getPointerOperand()->getType()->getPointerElementType());
								string pointerOp, opRet, position;
								raw_string_ostream rsptr(pointerOp), rsret(opRet), rspos(position);
								rsptr << PI->getPointerOperand()->getName();
								rsret << PI->getName();
								//If the first operand is 0, which is common, skip it.
								gep_type_iterator gepi= gep_type_begin(PI);
								if(cast<Constant>(gepi.getOperand())->isNullValue())
									gepi++;

								string op;
								if(registerTable.find(rsptr.str())!=registerTable.end())
									op =registerTable.find(rsptr.str())->second;
								else
									op=rsptr.str();

								if(Constant* CPV = dyn_cast<Constant>(gepi.getOperand()))
								{//If pos is a constant
									CPV->print(rspos);
									string auxi = rspos.str();
									for(int j=0; auxi[j]!=' '; auxi.erase(0,1));
									auxi.erase(0,1);
									position.clear();
									rspos.flush();
									rspos<<auxi;
								}
								else
								{	PI->print(rsdbg);
									errs() << "I can't translate that!\n" + rsdbg.str();
									return(false);
								}
								string instruction = op+".val"+rspos.str();
								registerTable.insert(pair<string,string>(rsret.str(),instruction));

							//Print the struct delcaration
								int currentElement=0;
								string strDecl;
								raw_string_ostream rsstructDeclaration(strDecl);

								string aux = sty->getName();
								while(aux[0]!='.') aux.erase(0,1);
								aux.erase(0,1);

								rsstructDeclaration << "struct " + aux + " {\n";
								bool alreadyDef = false;

								for(int i=0; i<globalStructs.size(); i++) //Check if the struct was already declared
								{	string aux=rsstructDeclaration.str();
									if (globalStructs[i].compare(0,aux.size(),aux)==0)
									{	alreadyDef=true;
										break;
									}
								}
								if(alreadyDef) //If true, continue translating instructions
									continue;

								for(StructType::element_iterator ib = sty->element_begin(); ib!=sty->element_end(); ib++, currentElement++)
								{	rsstructDeclaration<<"\t";
									Type *ty = *ib;
									//ty->print(rsdbg);

									string pointers="";

									if(ty->isPointerTy())
									{	while(ty->isPointerTy())
										{	pointers+='*';
											ty=ty->getPointerElementType();
										}
									}

									if(ty->isArrayTy())
									{
										vector<int> arraySizes;

										while(ty->isArrayTy())
										{
											arraySizes.push_back(ty->getArrayNumElements());
											ty = ty->getArrayElementType();
										}

										string varDef = "\t" + simpleInstType(ty) + pointers + " ";

										varDef+="val" + intToStr(currentElement);

										for(unsigned int i=0; i<arraySizes.size(); i++)
											varDef+="[" + intToStr(arraySizes[i]) + "]";
										varDef+=";\n";
										rsstructDeclaration << varDef;
									}
									else if(ty->isStructTy())
									{
										string structName = "val" + intToStr(currentElement);

										StructType *sty = dyn_cast<StructType>(ty);
										if(shouldRemoveStruct(F,sty))
											continue;
										string structTy=sty->getName();

										while(structTy[0]!='.') structTy.erase(0,1);
										structTy.erase(0,1);

										string strDef;
										raw_string_ostream rsst(strDef);

										rsstructDeclaration << "\tstruct " + structTy + pointers +" " + structName + ";\n";
									}
									else
									{	string varDef = "\t" + simpleInstType(ty) + pointers + " val" + intToStr(currentElement)+";\n";
									rsstructDeclaration<<varDef;
									}
								}
								rsstructDeclaration << "};\n\n";
								globalStructs.push_back(rsstructDeclaration.str());
							}
							else if(PI->getPointerOperand()->getType()->getPointerElementType()->isArrayTy())
							{
								string pointerOp, opRet, position;
								raw_string_ostream rsptr(pointerOp), rsret(opRet), rspos(position);
								rsptr << PI->getPointerOperand()->getName();
								rsret << PI->getName();
								//If the first operand is 0, which is common, skip it.
								gep_type_iterator gepi= gep_type_begin(PI);
								if(cast<Constant>(gepi.getOperand())->isNullValue())
									gepi++;

								string op;
								if(registerTable.find(rsptr.str())!=registerTable.end())
									op =registerTable.find(rsptr.str())->second;
								else
									op=rsptr.str();

								if(Constant* CPV = dyn_cast<Constant>(gepi.getOperand()))
								{//If pos is a constant
									CPV->print(rspos);
									string auxi = rspos.str();
									for(int j=0; auxi[j]!=' '; auxi.erase(0,1));
									auxi.erase(0,1);
									position.clear();
									rspos.flush();
									rspos<<auxi;
								}
								else
								{	rspos<<gepi.getOperand()->getName();
									string auxi=rspos.str();
									for(int i=0;i<auxi.size();i++)
										if(auxi[i]=='.') auxi[i]='_';
									position.clear();
									rspos.flush();
									rspos<<auxi;
								}
								string instruction = op+"["+rspos.str()+"]";
								registerTable.insert(pair<string,string>(rsret.str(),instruction));
							}

						}
						else if (ReturnInst* RI = dyn_cast<ReturnInst>(inst))
						{//Return instruction
							if(fun==0)
							{//If it's the new main()
								string prefix="loopCounter_";
								//Only look at loopCounters
								for(int i=0; i<definedVars.size();i++)
								//Add a printf loopcounter
								if(definedVars[i].compare(0,prefix.size(),prefix)==0)
									fileOutput+="\tprintf(\"" +  definedVars[i] + ": %d\\n\"," +  definedVars[i] + ");\n";

								//print return 0
								fileOutput+="\treturn (0);\n";
							}
							else
							{	string op0;
								raw_string_ostream rso0(op0);

								rso0 << RI->getOperand(0)->getName();

								op0=rso0.str();

								for(int i=0; i<op0.size(); i++)
									if (op0[i]=='.') op0[i]='_';

								Constant *CPV;
								if(Constant* CPV = dyn_cast<Constant>(RI->getOperand(0)))
								{//If b is a constant
									op0.clear();
									CPV->print(rso0);
									string auxi = rso0.str();
									for(int j=0; auxi[j]!=' '; auxi.erase(0,1));
									auxi.erase(0,1);
									str1.clear();
									rso0<<auxi;
								}


								inst->print(rso_inst);
								//Prints return(a);
								fileOutput+= "\treturn (" + op0 + ");\n";
							}
						}
						else if (BranchInst* BI = dyn_cast<BranchInst>(inst))
						{//BR instruction
							string brfileOutput="";
							if(inst->getNumOperands()==1)
							{//If it's a 'br label' instruction
								//Get the sucessor basicblock
								rso_inst<<BI->getSuccessor(0)->getName();
								string branchName = rso_inst.str();

								//Change '.' to '_'
								for(int i=0; i<branchName.size(); i++)
									if (branchName[i]=='.') branchName[i]='_';

								//Get an iterator cointaing the next BB
								Function::iterator nextBlock = bb;
								nextBlock++;

								//If the sucessor is the next basicblock, then we don't need a goto
								if(BI->getSuccessor(0)->getName() != nextBlock->getName())
									brfileOutput+="\tgoto "+branchName+";\n";
							}
							else
							{//If it's 'br condition labeltrue labelfalse'
								//Get condition
								string name=BI->getCondition()->getName();
								for(int i=0; i<name.size(); i++)
									if (name[i]=='.') name[i]='_';
								if(name.empty())
								{//If the second operand is a register
									string aux;
									raw_string_ostream rsaux(aux);
									BI->getCondition()->print(rsaux);
									//Get the variable associated to the register
									name=registerTable.find(rsaux.str())->second;
								}
								else if(findValue(name,definedVars)==-1)
									name=registerTable.find(name)->second;
								//for(int i=0; i<name.size(); i++)
								//	if (name[i]=='.') name[i]='_';

								//Get iftrue
								rso_inst<<BI->getSuccessor(0)->getName();
								std::string str2;
								llvm::raw_string_ostream rso_inst2(str2);
								//Get iffalse
								rso_inst2<<BI->getSuccessor(1)->getName();

								//Change '.' to '_'
								string branchNameTrue = rso_inst.str();
								for(int i=0; i<branchNameTrue.size(); i++)
									if (branchNameTrue[i]=='.') branchNameTrue[i]='_';

								string branchNameFalse = rso_inst2.str();
								for(int i=0; i<branchNameFalse.size(); i++)
									if (branchNameFalse[i]=='.') branchNameFalse[i]='_';

								//Get an iterator containing the next block
								Function::iterator nextBlock = bb;
								nextBlock++;

								//If the sucessor is the next basicblock, then we don't need a goto
								if(nextBlock->getName() == BI->getSuccessor(0)->getName())
									brfileOutput+="\tif(!" + name + "){\n\t\tgoto " + branchNameFalse + ";\n\t}\n";
								else if (nextBlock->getName() == BI->getSuccessor(1)->getName())
									brfileOutput+="\tif(" + name + "){\n\t\tgoto " + branchNameTrue + ";\n\t}\n";
								else
									brfileOutput+="\tif(" + name + "){\n\t\tgoto " + branchNameTrue + ";\n\t}\n\telse{\n\t\tgoto " + branchNameFalse + ";\n\t}\n";
							}
							fileBROutMap.find(bb)->second=brfileOutput;
						}
						else if (AllocaInst* AI = dyn_cast<AllocaInst>(inst))
						{//Alloc instruction
							//Creates a variable declaration in the beggining of the program.
							//AllocaInst *AI;
							//errs() << simpleInstType(AI->getType());
							if(AI->getType()->getPointerElementType()->isArrayTy() || AI->getType()->isArrayTy())
							{	Type * arrayTy = AI->getAllocatedType();
								vector<int> arraySizes;

								while(arrayTy->isArrayTy())
								{
									arraySizes.push_back(arrayTy->getArrayNumElements());
									arrayTy = arrayTy->getArrayElementType();
								}

								string varDef = "\t" + simpleInstType(arrayTy) + " ";

								string aux=AI->getName();
								for(int i=0; i<aux.size(); i++)
									if (aux[i]=='.') aux[i]='_';

								varDef+=aux;

								for(unsigned int i=0; i<arraySizes.size(); i++)
									varDef+="[" + intToStr(arraySizes[i]) + "]";
								varDef+=";\n";
								variableDeclarations.push_back(varDef);
							}
							else if (AI->getType()->getPointerElementType()->isStructTy() || AI->getType()->isStructTy())
							{
								string structName = AI->getName();

								string structTy;
								if(AI->getType()->isStructTy())
								{	StructType *sty = dyn_cast<StructType>(AI->getType());
									structTy=sty->getName();
								}
								else
								{	StructType *sty = dyn_cast<StructType>(AI->getType()->getPointerElementType());
									structTy=sty->getName();
								}

								while(structTy[0]!='.') structTy.erase(0,1);
								structTy.erase(0,1);

								string strDef;
								raw_string_ostream rsst(strDef);

								rsst<<"\tstruct " + structTy + " " + structName + ";\n";
								variableDeclarations.push_back(rsst.str());
							}
							else
							{
								string varDef="\t";
								varDef+=simpleInstType(AI->getType()->getElementType()) +" ";

								string aux=AI->getName();
								for(int i=0; i<aux.size(); i++)
									if (aux[i]=='.') aux[i]='_';

								definedVars.push_back(aux);
								varDef+= aux + ";\n";
								variableDeclarations.push_back(varDef);
							}
						}
						else if (StoreInst* SI = dyn_cast<StoreInst>(inst))
						{//Store instruction
							//Prints a = b;

							string str0, str1;
							raw_string_ostream rso0(str0), rso1(str1);

							//Get a.
							rso0<<SI->getOperand(1)->getName();

							string op0=rso0.str();

							for(int i=0; i<op0.size(); i++)
								if (op0[i]=='.') op0[i]='_';

							//Get b
							Constant *CPV;
							if(Constant* CPV = dyn_cast<Constant>(SI->getOperand(0)))
							{//If b is a constant
								CPV->print(rso1);
								string auxi = rso1.str();
								for(int j=0; auxi[j]!=' '; auxi.erase(0,1));
								auxi.erase(0,1);
								str1.clear();
								rso1<<auxi;
							}
							else
							{	Function::arg_iterator ab=F->arg_begin();
								Function::arg_iterator ae=F->arg_end();
								rso1<<SI->getOperand(0)->getName();
							}

							string op1=rso1.str();
							for(int i=0; i<op1.size(); i++)
								if (op1[i]=='.') op1[i]='_';

							if(registerTable.find(op1)!=registerTable.end())
								op1=registerTable.find(op1)->second;

							if(registerTable.find(op0)!=registerTable.end())
								op0=registerTable.find(op0)->second;

							//Prints a = b;
							fileOutput+= "\t" + op0 + " = " + op1 + ";\n";

							}
						else if (BinaryOperator* BO = dyn_cast<BinaryOperator>(inst))
						{//Binary operations like add, sub, etc
							string operation;
							switch (inst->getOpcode()){

							case Instruction::Add:
							case Instruction::FAdd: operation = " + "; break;
							case Instruction::Sub:
							case Instruction::FSub: operation = " - "; break;
							case Instruction::Mul:
							case Instruction::FMul: operation = " * "; break;
							case Instruction::URem:
							case Instruction::SRem:
							case Instruction::FRem: operation = " % "; break;
							case Instruction::UDiv:
							case Instruction::SDiv:
							case Instruction::FDiv: operation = " / "; break;
							case Instruction::And: 	operation = " & "; break;
							case Instruction::Or: 	operation = " | "; break;
							case Instruction::Xor: 	operation = " ^ "; break;
							case Instruction::Shl : operation = " << "; break;
							case Instruction::LShr:
							case Instruction::AShr: operation = " >> "; break;
							}

							string boDest=BO->getName();
							bool isRegister=false;
							if(findValue(boDest,definedVars)==-1)
							{//If the variable recieving the comparation wasn't defined till now
								//Add it to our definedVars vector and print is declaration in the beggining of the program
								string varDef="\t";
								varDef+=simpleInstType(BO->getType()) +" ";
								isRegister=true;
								//definedVars.push_back(boDest);
								varDef+= boDest + ";\n";
								variableDeclarations.push_back(varDef);
							}
							// Print a =
							rso_inst<<boDest + " = ";

							string op0, op1;
							raw_string_ostream rsop0(op0), rsop1(op1);

							Constant *CPV;
							if(Constant* CPV = dyn_cast<Constant>(BO->getOperand(0)))
							{//If the first operand is a constant
								CPV->print(rsop0);
								string auxi = rsop0.str();
								for(int j=0; auxi[j]!=' ' && j<auxi.size(); auxi.erase(0,1));
								auxi.erase(0,1);
								if(!auxi.empty())
								{	op0.clear();
									rsop0<<auxi;
								}
							}
							else
							{	rsop0<<BO->getOperand(0)->getName();
								op0=rsop0.str();
								for(int i=0; i<op0.size(); i++)
									if (op0[i]=='.') op0[i]='_';
								if(op0.empty())
								{//If the first operand is a register
									string aux;
									raw_string_ostream rsaux(aux);
									BO->getOperand(0)->print(rsaux);
									//Get register associated variable in our registerTable
									op0=registerTable.find(rsaux.str())->second;
								}

							}

							if(Constant* CPV = dyn_cast<Constant>(BO->getOperand(1)))
							{//If the second operand is a constant
								CPV->print(rsop1);
								string auxi = rsop1.str();
								for(int j=0; auxi[j]!=' ' && j<auxi.size(); auxi.erase(0,1));
								auxi.erase(0,1);
								if(!auxi.empty())
								{	op1.clear();
									rsop1<<auxi;
								}
							}
							else
							{	rsop1<<BO->getOperand(1)->getName();
								op1=rsop1.str();
								for(int i=0; i<op1.size(); i++)
									if (op1[i]=='.') op1[i]='_';
								if(op1.empty())
								{//If the second operand is a register
									string aux;
									raw_string_ostream rsaux(aux);
									BO->getOperand(1)->print(rsaux);
									//Get the variable associanted with the register
									op1=registerTable.find(rsaux.str())->second;
								}

							}
							//Prints a = b op c;
							fileOutput+= "\t"+rso_inst.str() +" (" + rsop0.str()+ ")" +operation +"("+ rsop1.str()+");\n";
							if(isRegister)
							{	string complement= rsop0.str() + operation + rsop1.str();
								registerTable.insert(pair<string,string>(boDest,complement));
								//errs()<<"_"+boDest+"_\n";
							}
						}
						else if (CmpInst* CI = dyn_cast<CmpInst>(inst))
						{//Compare instruction, like '<', '==', etc
							//CmpInst* CI;
							string operation;
							switch (CI->getPredicate()) {
								case ICmpInst::FCMP_UEQ:
								case ICmpInst::FCMP_OEQ:
								case ICmpInst::ICMP_EQ: operation =  " == "; break;
								case ICmpInst::FCMP_UNE:
								case ICmpInst::FCMP_ONE:
								case ICmpInst::ICMP_NE: operation =  " != "; break;
								case ICmpInst::ICMP_ULE:
								case ICmpInst::FCMP_ULE:
								case ICmpInst::FCMP_OLE:
								case ICmpInst::ICMP_SLE: operation =  " <= "; break;
								case ICmpInst::ICMP_UGE:
								case ICmpInst::FCMP_UGE:
								case ICmpInst::FCMP_OGE:
								case ICmpInst::ICMP_SGE: operation =  " >= "; break;
								case ICmpInst::ICMP_ULT:
								case ICmpInst::FCMP_ULT:
								case ICmpInst::FCMP_OLT:
								case ICmpInst::ICMP_SLT: operation =  " < "; break;
								case ICmpInst::ICMP_UGT:
								case ICmpInst::FCMP_UGT:
								case ICmpInst::FCMP_OGT:
								case ICmpInst::ICMP_SGT: operation =  " > "; break;
							}
							string cmpDest=CI->getName();

							bool isRegister = false;
							if(findValue(cmpDest,definedVars)==-1)
							{//If the variable recieving the comparation wasn't defined till now
								//Add it to our register table
								isRegister=true;
							}

							rso_inst<<cmpDest + " = ";

							string op0, op1;
							raw_string_ostream rsop0(op0), rsop1(op1);

							Constant *CPV;
							if(Constant* CPV = dyn_cast<Constant>(CI->getOperand(0)))
							{//If the first operand is a constant
								CPV->print(rsop0);
								string auxi = rsop0.str();
								for(int j=0; auxi[j]!=' ' && j<auxi.size(); auxi.erase(0,1));
								auxi.erase(0,1);
								if(!auxi.empty())
								{	op0.clear();
									rsop0<<auxi;
								}
							}
							else
							{	rsop0<<CI->getOperand(0)->getName();
								op0=rsop0.str();
								for(int i=0; i<op0.size(); i++)
									if (op0[i]=='.') op0[i]='_';
								if(op0.empty())
								{//If the first operand is a register
									string aux;
									raw_string_ostream rsaux(aux);
									CI->getOperand(0)->print(rsaux);
									//Get the variable associanted with the register
									op0=registerTable.find(rsaux.str())->second;
								}
								else if ( findValue(op0,definedVars)==-1)
									op0="(" + registerTable.find(op0)->second + ")";

								//for(int i=0; i<op0.size(); i++)
								//	if (op0[i]=='.') op0[i]='_';
							}

							if(Constant* CPV = dyn_cast<Constant>(CI->getOperand(1)))
							{//If the second operand is a constant
								CPV->print(rsop1);
								string auxi = rsop1.str();
								for(int j=0; auxi[j]!=' ' && j<auxi.size(); auxi.erase(0,1));
								auxi.erase(0,1);
								if(!auxi.empty())
								{	op1.clear();
									rsop1<<auxi;
								}
							}
							else
							{	rsop1<<CI->getOperand(1)->getName();
								op1=rsop1.str();
								for(int i=0; i<op1.size(); i++)
									if (op1[i]=='.') op1[i]='_';
								if(op1.empty())
								{//If the second operand is a register
									string aux;
									raw_string_ostream rsaux(aux);
									CI->getOperand(1)->print(rsaux);
									//Get the variable associated to the register
									op1=registerTable.find(rsaux.str())->second;
								}
								else if ( findValue(op1,definedVars)==-1)
									op1="(" + registerTable.find(op1)->second + ")";
								//for(int i=0; i<op1.size(); i++)
								//	if (op1[i]=='.') op1[i]='_';
							}
							//Prints a = b op c;
							string complement =  rsop0.str() + operation  + rsop1.str() ;
							if(!isRegister)
								fileOutput+="\t" + rso_inst.str() +complement +";\n";
							else
							{	string aux=CI->getName();
								registerTable.insert(pair<string,string>(aux,complement));
							}
						}
						else if (LoadInst* LI = dyn_cast<LoadInst>(inst))
						{//Load inst
							string tab1,tab2;
							raw_string_ostream rtab1(tab1), rtab2(tab2);
							//Get the register recieving the Load
							LI->print(rtab1);
							//Get the variable being loaded
							if(registerTable.find(LI->getOperand(0)->getName())!=registerTable.end())
								rtab2<<registerTable.find(LI->getOperand(0)->getName())->second;
							else
								rtab2<<LI->getOperand(0)->getName();

							//Create a reference Register-Variable in our registerTable
							registerTable.insert(pair<string,string>(rtab1.str(),rtab2.str()));
						}
						else if(PHINode* PN = dyn_cast<PHINode>(inst))
						{	//PHINode * PN;

							string phind=inst->getName();

							for(int i=0; i<phind.size(); i++)
								if(phind[i]=='.')	phind[i]='_';

							if(phind.empty())
							{//If the variable recieving phi is a register
								//Get the register number
								string reg;
								raw_string_ostream rsreg(reg);
								//Get the register recieving the Load
								inst->print(rsreg);
								while(reg[0]!='%')
									reg.erase(0,1);
								reg.erase(0,1);
								int i;
								for(i=reg.size()-1; reg[i]!='=';i--)
									reg.erase(i,1);
								reg.erase(i-1,2);
								//phind = aux'register number'
								phind="aux"+reg;

								reg.clear();
								PN->print(rsreg);
								registerTable.insert(pair<string,string>(rsreg.str(),phind));
							}

							string phitype=simpleInstType(PN->getType());

							if(findValue(phind,definedVars)==-1)
							{//If the variable recieving the comparation wasn't defined till now
								//Add it to our definedVars vector and print its declaration in the beggining of the program
								string varDef = "\t";
								varDef+=phitype +" ";
								definedVars.push_back(phind);
								varDef+= phind + ";\n";
								variableDeclarations.push_back(varDef);
							}

							/*string phiaux=phind+"_phi";
							string varDef="\t" + phitype + " " + phiaux + ";\n";
							variableDeclarations.push_back(varDef);
							definedVars.push_back(phiaux);

							fileOutput+= "\t" + phind + " = " + phiaux + ";\n";
							*/

							string phiaux=phind;

							for(PHINode::block_iterator blockit = PN->block_begin(); blockit!=PN->block_end(); blockit++)
							{
								string st1;
								raw_string_ostream rst1(st1);
								BasicBlock *block=*blockit;

								if(Constant* CPV = dyn_cast<Constant>(PN->getIncomingValueForBlock(block)))
								{//If the operand is a constant
									CPV->print(rst1);
									string auxi = rst1.str();
									for(int j=0; auxi[j]!=' ' && j<auxi.size(); auxi.erase(0,1));
									auxi.erase(0,1);
									if(!auxi.empty())
									{	st1.clear();
										rst1<<auxi;
									}
								}
								else
								{	rst1<<PN->getIncomingValueForBlock(block)->getName();
									string val=rst1.str();
									for(int i=0; i<val.size(); i++)
										if (val[i]=='.') val[i]='_';
									string aux=val;

									if(val.empty())
									{//Its a register
										string reg;
										raw_string_ostream rsreg(reg);
										PN->getIncomingValueForBlock(block)->print(rsreg);
										val=registerTable.find(rsreg.str())->second;
									}
									else if(findValue(val,definedVars)==-1)
									{
										if(registerTable.find(val)==registerTable.end())
											val=aux;
										else
											val=registerTable.find(val)->second;
									}
									st1.clear();
									rst1<<val;
								}
								fileOutMap.find(block)->second += "\t" + phiaux + " = " + rst1.str() + ";\n";
							}
						}
						else if(CallInst* CaI = dyn_cast<CallInst>(inst))
						{	//CallInst* CaI;

							Function* callFun = CaI->getCalledFunction();
							for(Module::iterator cf=M.begin(); cf!=M.end(); ++cf)
							{	if(cf->getName() == callFun->getName())
								{	cf->getName();
									bool notOnVector=true;
									for(int j=0; j<shouldPrintFun.size();j++)
									{	if(shouldPrintFun[j]->getName()==cf->getName())
										{	notOnVector=false;
											break;
										}
									}
									if(notOnVector)
										shouldPrintFun.push_back(cf);
									break;
								}
							}
							//CallInst* CaI;

							string funNm, callRet, opRet;
							raw_string_ostream rsfnm(funNm);
							raw_string_ostream rscall(callRet);
							raw_string_ostream rsop(opRet);

							rsfnm << callFun->getName();
							rscall << CaI->getName();
							callRet=rscall.str();
							fileOutput+="\t";
							string fTy = simpleInstType(callFun->getReturnType());
							if (!callRet.empty())
							{	fileOutput+= callRet + " = ";
								string varDef = "\t";
								varDef+=fTy + " ";
								definedVars.push_back(callRet);
								varDef+= callRet + ";\n";
								variableDeclarations.push_back(varDef);
							}
							fileOutput+= rsfnm.str() +"(";

							CallInst::op_iterator op=CaI->op_begin();
							CallInst::op_iterator opend=CaI->op_end();

							//The last operand is the called function intself, we only want the args
							opend--;

							for(; op!=opend; ++op)
							{	opRet.clear();
								if(Constant* CPV = dyn_cast<Constant>(op))
								{//If the operand is a constant
									CPV->print(rsop);
									string auxi = rsop.str();
									for(int j=0; auxi[j]!=' ' && j<auxi.size(); auxi.erase(0,1));
									auxi.erase(0,1);
									if(!auxi.empty())
									{	opRet.clear();
										rsop<<auxi;
									}
								}
								else
								{	rsop << op->get()->getName();
									string auxi=rsop.str();
									for(int i=0; i<auxi.size();i++)
										if(auxi[i]=='.') auxi[i]='_';
									opRet.clear();

									if(auxi.empty())
									{//If the first operand is a register
										string regaux;
										raw_string_ostream rsaux(regaux);
										op->get()->print(rsaux);
										//Get register associated variable in our registerTable
										auxi=registerTable.find(rsaux.str())->second;
									}
									rsop<<auxi;
								}
								if(op!=CaI->op_begin())
										fileOutput+=",";
								fileOutput+=rsop.str();
							}
							fileOutput+=");\n";
						}
						else
						{	inst->print(rso_inst);
							fileOutput+= "//" + rso_inst.str() + "\n";
						}

					}
					fileOutput+=fileOutMap.find(bb)->second;
					fileOutMap.find(bb)->second=fileOutput;
				}

				string fileOutput="";

				for(Function::iterator bb=F->begin(), be=F->end();bb!=be;++bb)
				{	fileOutput+=fileOutMap.find(bb)->second;
					fileOutput+=fileBROutMap.find(bb)->second;
				}
				//Adds the final '}'
				fileOutput+="}\n\n";
				//Prints everything we analysed
				for(int i=0; i<variableDeclarations.size();i++)
					funBody<<variableDeclarations[i];

				funBody<<fileOutput;
				errs() << "Done translating " + F->getName()+"\n";
			}
			//Prints on screen a masage to the user.
			outp<<header;
			outp<<funDeclarations.str();
			outp<<globalVariables;
			for(unsigned int i=0; i<globalStructs.size(); i++)
				outp<<globalStructs[i];
			outp<<funBody.str();
			outp.close();

			//for(map<string,string>::iterator it = registerTable.begin(); it!=registerTable.end(); ++it)
			//	errs() << it->first + "\t" + it->second + "\n";


			errs() << "\nFile printed with sucess\n";
		}
		return (false);
    }
  };
}

char BytecodeTranslator::ID = 0;
static RegisterPass<BytecodeTranslator> X("BytecodeTranslator", "Backend translator from BC to C", false, false);
