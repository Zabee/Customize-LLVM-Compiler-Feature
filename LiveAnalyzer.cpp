#include "llvm/Module.h"
#include "llvm/Instructions.h"
#include "llvm/IntrinsicInst.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Analysis/InlineCost.h"
#include "llvm/DataLayout.h"
#include "llvm/Target/TargetLibraryInfo.h"
#include "llvm/Transforms/IPO/InlinerPass.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/Local.h"
#include "llvm/Support/CallSite.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Support/InstIterator.h"
#include "llvm/User.h"
#include "llvm/Type.h"
#include "llvm/Bitcode/Archive.h"
#include "llvm/Support/Format.h"
#include "llvm/Support/Host.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Support/TargetRegistry.h"
#include "llvm/Target/TargetRegisterInfo.h"
#include "llvm/Target/TargetMachine.h"
#include "llvm/Target/TargetLowering.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/CodeGen/Analysis.h"
#include "llvm/CodeGen/ValueTypes.h"

#include <vector>
#include <limits.h>
#include <stdlib.h>
#include <string.h>

#define LLVM_VERSION(major, minor) (((major) << 8) | (minor))
#define LLVM_VERSION_CODE LLVM_VERSION(LLVM_VERSION_MAJOR, LLVM_VERSION_MINOR)

using namespace llvm;
using namespace std;
namespace 
{

	//Liveness Analyzer Class
	class LiveAnalyzer 
	{
		const TargetLowering *TLI;
		const TargetRegisterInfo* TRI;
		const TargetMachine *TMI;
		unsigned I8MaxLive,I16MaxLive,I32MaxLive,I64MaxLive,F32MaxLive,F64MaxLive;
		unsigned getI8RegNum()
		{
			const TargetRegisterClass *RC = TRI->getRegClass(0);
			unsigned NumRegs = RC->getNumRegs();
//			errs() << "I8RegClassNumRegs " << NumRegs << "\n";
			return NumRegs;
			
		}		
		unsigned getI16RegNum()
		{
			const TargetRegisterClass *RC = TRI->getRegClass(4);
			unsigned NumRegs = RC->getNumRegs();
//			errs() << RC->getID() << "\t" << strcmp(RC->getName(),"GR16") << "\n";
/*			errs() << "I16RegClassNumRegs " << NumRegs << "\n";
			errs() << *TRI->getRegClassPressureSets(RC) << "\n";
			errs() << TRI->getRegClassWeight(RC).RegWeight << "\n";			
			errs() << TRI->getRegClassWeight(RC).WeightLimit << "\n";				*/
			return NumRegs;			
		}
		unsigned getI32RegNum()
		{
			const TargetRegisterClass *RC = TRI->getRegClass(10);
			unsigned NumRegs = RC->getNumRegs();
//			errs() << "I32RegClassNumRegs " << NumRegs << "\n";
			return NumRegs;			
		}
		unsigned getI64RegNum()
		{
			const TargetRegisterClass *RC = TRI->getRegClass(28);
			unsigned NumRegs = RC->getNumRegs();
/*			errs() << "I64RegClassNumRegs " << NumRegs << "\n";
			errs() << *TRI->getRegClassPressureSets(RC) << "\n";
			errs() << TRI->getRegClassWeight(RC).RegWeight << "\n";*/
			return NumRegs;			
		}
		unsigned getF32RegNum()
		{
			const TargetRegisterClass *RC = TRI->getRegClass(9);
			unsigned NumRegs = RC->getNumRegs();
/*			errs() << "F32RegClassNumRegs " << NumRegs << "\n";
			errs() << *TRI->getRegClassPressureSets(RC) << "\n";
			errs() << TRI->getRegClassWeight(RC).RegWeight << "\n";*/
			return NumRegs;			
		}
		unsigned getF64RegNum()
		{
			const TargetRegisterClass *RC = TRI->getRegClass(30);
			unsigned NumRegs = RC->getNumRegs();
/*			errs() << "F64RegClassNumRegs " << NumRegs << "\n";
			errs() << TRI->getNumRegPressureSets() << "\n";
			errs() << *TRI->getRegClassPressureSets(RC) << "\n";
			errs() << TRI->getRegClassWeight(RC).RegWeight << "\n";			
			errs() << TRI->getRegClassWeight(RC).WeightLimit << "\n";*/
			return NumRegs;			
		}			
		void dump(vector<Instruction*> Insts)
		{
			for(vector<Instruction*>::iterator II = Insts.begin(),IE = Insts.end();
				II != IE; ++II)
			{
				errs() << **II << "\n";
			}
			errs() << "\n";			
		}
		vector<Instruction*> reverse(vector<Instruction*> Insts)
		{
			vector<Instruction*> IValues;
			unsigned i = Insts.size();
			for(--i;i>0;--i)
			{
				IValues.push_back(Insts[i]);
//				errs() << *Insts[i] << "\n";
			}
			IValues.push_back(Insts[0]);
			return IValues;
		}
		vector<Instruction*> visitFunction(vector<Instruction*> Insts,Function *Callee)
		{
			vector<Instruction*> IValues;
			// BB is a pointer to a BasicBlock instance
			for (Function::iterator BB = Callee->begin(), BE = Callee->end(); BB != BE; ++BB)
			{
				// II is a pointer to a Instruction instance		
				for (BasicBlock::iterator II = BB->begin(), IE = BB->end(); II != IE; ++II )
				{
					//errs() << *II << "\n";
					for(vector<Instruction*>::iterator FI = Insts.begin(),FE = Insts.end();
						FI != FE; ++FI)
					{
						Instruction *I1 = II;
						Instruction *I2 = *FI;
						if(I1 == I2)
						{
							IValues.push_back(II);
							break;
						}
					}
				}
			}
			return 	IValues;
		}
		vector<Instruction*> visit(vector<Instruction*> Insts,Function *Callee)
		{
			vector<Instruction*> IValues;
			for(vector<Instruction*>::iterator II = Insts.begin(),IE = Insts.end();
				II != IE; ++II)
			{
				Instruction *I1 = *II;
				IValues.push_back(I1);				
//				errs() << "Instuction " << **II << "\n";// << (*II)->getOpcodeName() << " Instruction\n";
				for (User::op_iterator OI = (*II)->op_begin(), OE = (*II)->op_end(); OI!=OE;++OI)
//				for(unsigned i = 0; i < (*II)->getNumOperands(); ++i)
				{
//					Value *v = (*II)->getOperand(i);
					Value *v = *OI;
					Type *Ty = v->getType();
//					errs() << "Operand " << *v << "\t" << *v->getType() << " operand\n";
					if(Ty == Type::getLabelTy(Callee->getContext()))
					{
						continue;
//						errs() << "Operand\t" << v->getType()->isLabelTy();
					}	
					else  if (isa<Constant>(v) || isa<Argument>(v) || isa<GlobalValue>(v))
					{
						continue;					
//						errs() << "not label\t" << *(*OI) << "\n";
					}
					else
					{
						bool flag2 = false;
						for(vector<Instruction*>::iterator FI = Insts.begin(),FE = Insts.end();
							FI != FE; ++FI)
						{
							Value *u = *FI;
							if(v == u)
							{
								flag2 = true;
								break;
							}
						}
						if(!flag2)
						{
//							errs() << **OI << "\n";
							if (Instruction *VI = dyn_cast<Instruction>(v))	
							{
								IValues.push_back(VI);
//								errs() << *VI << "\n";
							}
						}
					}
				}
//				errs() << "\n";
			}
//			errs() << "Enters getMaxLiveCount";
			return visitFunction(IValues,Callee);
		}
		//analyzeFunction - analyze Function a and divide the function as per the type of instrunctions
		void analyzeFunction(Function *Callee);
		//getLiveCount - return Maximum Live variables count Of the Function
		unsigned getLiveCount(Function *Callee);
		unsigned getMaxLiveCount(vector<Instruction*> Insts,Function *Callee,Type *Ty1,Type *Ty2);
		public :
		LiveAnalyzer()
		{
			#if LLVM_VERSION_CODE >= LLVM_VERSION(2, 9)
			  std::string Err;
			#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 1)
			  std::string HostTriple = sys::getDefaultTargetTriple();
			#else
			  std::string HostTriple = sys::getHostTriple();
			#endif
			const Target *NativeTarget = TargetRegistry::lookupTarget(HostTriple, Err);
			if (NativeTarget == 0) {
			    llvm::errs() << "Warning: unable to select native target: " << Err << "\n";
			    TLI = 0;
			} else {
			#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 1)
			    TargetMachine *TM = NativeTarget->createTargetMachine(HostTriple, "", "",
				                                                          TargetOptions());
			#elif LLVM_VERSION_CODE >= LLVM_VERSION(3, 0)
			    TargetMachine *TM = NativeTarget->createTargetMachine(HostTriple, "", "");
			#else
			    TargetMachine *TM = NativeTarget->createTargetMachine(HostTriple, "");
			#endif
			    TLI = TM->getTargetLowering();
			}
			#endif	
			TMI = &TLI->getTargetMachine();			
			TRI = TMI->getRegisterInfo();
		}
		//analyzeCallSite - analyze Call site for Live Variables Count.
		//return true if there is Excess in Live element Count than Number of registers.
		//return false otherwise.
		double analyzeCallSite(CallSite CS) 
		{
			unsigned NumRegs = TRI->getNumRegs();
			Function *Caller = CS.getCaller();
			Function *Callee = CS.getCalledFunction();
			unsigned I8MaxLiveCallee,I16MaxLiveCallee,I32MaxLiveCallee,I64MaxLiveCallee,F32MaxLiveCallee,F64MaxLiveCallee;
			unsigned I8MaxLiveCaller,I16MaxLiveCaller,I32MaxLiveCaller,I64MaxLiveCaller,F32MaxLiveCaller,F64MaxLiveCaller;			
			unsigned MaxLiveInCaller = getLiveCount(Caller);
			unsigned MaxLiveInCallee = getLiveCount(Callee);	    
			if(NumRegs < (MaxLiveInCaller + MaxLiveInCallee))
				return ((double)(MaxLiveInCaller + MaxLiveInCallee - NumRegs)/(double)NumRegs);
       			analyzeFunction(Callee);
       			I8MaxLiveCallee = I8MaxLive;
       			I16MaxLiveCallee = I16MaxLive;
       			I32MaxLiveCallee = I32MaxLive;
       			I64MaxLiveCallee = I64MaxLive;
			F32MaxLiveCallee = F32MaxLive;
			F64MaxLiveCallee = F64MaxLive;
       			analyzeFunction(Caller);      
       			I8MaxLiveCaller = I8MaxLive;
       			I16MaxLiveCaller = I16MaxLive;
       			I32MaxLiveCaller = I32MaxLive;
       			I64MaxLiveCaller = I64MaxLive;
			F32MaxLiveCaller = F32MaxLive;
			F64MaxLiveCaller = F64MaxLive; 	
			unsigned NumRegSpil = 0, NumSpilRegCls = 0;
			unsigned NumI8Reg = getI8RegNum();
			if((NumI8Reg < (I8MaxLiveCallee + I8MaxLiveCaller)))
			{
				NumRegSpil +=  (I8MaxLiveCallee + I8MaxLiveCaller - NumI8Reg);
				NumSpilRegCls += NumI8Reg;
			}	
			unsigned NumI16Reg = getI16RegNum();
			if((NumI16Reg < (I16MaxLiveCallee + I16MaxLiveCaller)))
			{
				NumRegSpil +=  (I16MaxLiveCallee + I16MaxLiveCaller - NumI16Reg);
				NumSpilRegCls += NumI16Reg;
			}
			unsigned NumI32Reg = getI32RegNum();
			if((NumI32Reg < (I32MaxLiveCallee + I32MaxLiveCaller)))
			{
				NumRegSpil +=  (I32MaxLiveCallee + I32MaxLiveCaller - NumI32Reg);
				NumSpilRegCls += NumI32Reg;
			}
			unsigned NumI64Reg = getI64RegNum();
			if((NumI64Reg < (I64MaxLiveCallee + I64MaxLiveCaller)))
			{
				NumRegSpil +=  (I64MaxLiveCallee + I64MaxLiveCaller - NumI64Reg);
				NumSpilRegCls += NumI64Reg;
			}
			unsigned NumF32Reg = getF32RegNum();
			if((NumF32Reg < (F32MaxLiveCallee + F32MaxLiveCaller)))
			{
				NumRegSpil +=  (F32MaxLiveCallee + F32MaxLiveCaller - NumF32Reg);
				NumSpilRegCls += NumF32Reg;
			}
			unsigned NumF64Reg = getF64RegNum();
			if((NumF64Reg < (F64MaxLiveCallee + F64MaxLiveCaller)))
			{
				NumRegSpil +=  (F64MaxLiveCallee + F64MaxLiveCaller - NumF64Reg);
				NumSpilRegCls += NumF64Reg;
			}
			if(NumSpilRegCls != 0)
				return ((double)NumRegSpil)/((double)NumSpilRegCls);
			return 0;
		}
	};
	void LiveAnalyzer :: analyzeFunction(Function *Callee)
	{
		I8MaxLive = I16MaxLive = I32MaxLive = I64MaxLive = F32MaxLive = F64MaxLive = 0;
		vector<Instruction*> I8Inst;
		vector<Instruction*> I16Inst;		
		vector<Instruction*> I64Inst;
		vector<Instruction*> F32Inst;		
		vector<Instruction*> F64Inst;
		vector<Instruction*> I32Inst;
		// BB is a pointer to a BasicBlock instance
		for (Function::iterator BB = Callee->begin(), BE = Callee->end(); BB != BE; ++BB)
		{
			// II is a pointer to a Instruction instance		
			for (BasicBlock::iterator II = BB->begin(), IE = BB->end(); II != IE; ++II )
			{
//				errs() << *II << "\n";
				if(II->getOpcode() == Instruction::Alloca)
				{
					continue;
				}
				else
				{
					for (User::op_iterator OI = II->op_begin(), OE = II->op_end(); OI!=OE;++OI)
					{
						Value *v = *OI;
						Type *Ty = v->getType();
//						Type::TypeID  TypId = Ty->getTypeID();
						if(Ty->isIntegerTy())
						{
							if(Ty == Type::getInt1Ty(Callee->getContext()) || Ty == Type::getInt8Ty(Callee->getContext()))
							{
								I8Inst.push_back(II);	
							}
							else if(Ty == Type::getInt16Ty(Callee->getContext()))
							{
								I16Inst.push_back(II);	
							}
							else if(Ty == Type::getInt32Ty(Callee->getContext()))
							{
								I32Inst.push_back(II);	
							}
							else if(Ty == Type::getInt64Ty(Callee->getContext()))
							{
								I64Inst.push_back(II);	
							}
						}
						if(Ty->isFloatingPointTy())
						{
//							errs()<< *II << " float\n";
							if(Ty == Type::getDoubleTy(Callee->getContext()))
							{
								F64Inst.push_back(II);	
							}
							else 
							{
								F32Inst.push_back(II);	
							}
						}
					}
					
				}
			}
		}
//		dump(reverse(visit(I16Inst,Callee)));
//		errs() << "come character\n";
		I8MaxLive = getMaxLiveCount(visit(I8Inst,Callee),Callee,Type::getInt1Ty(Callee->getContext()),Type::getInt8Ty(Callee->getContext()));
//		errs() << "come short \n";
		I16MaxLive = getMaxLiveCount(visit(I16Inst,Callee),Callee,Type::getInt16Ty(Callee->getContext()),Type::getVoidTy(Callee->getContext()));
//		errs() << "come i32\n";
		I32MaxLive = getMaxLiveCount(visit(I32Inst,Callee),Callee,Type::getInt32Ty(Callee->getContext()),Type::getVoidTy(Callee->getContext()));
//		errs() << "come  i64 \n";
		I64MaxLive = getMaxLiveCount(visit(I64Inst,Callee),Callee,Type::getInt64Ty(Callee->getContext()),Type::getVoidTy(Callee->getContext()));
//		errs() << "come float \n";
		F32MaxLive = getMaxLiveCount(visit(F32Inst,Callee),Callee,Type::getFloatTy(Callee->getContext()),Type::getVoidTy(Callee->getContext()));
//		errs() << "come double \n";
		F64MaxLive = getMaxLiveCount(visit(F64Inst,Callee),Callee,Type::getDoubleTy(Callee->getContext()),Type::getVoidTy(Callee->getContext()));
//		errs() << "I8MaxLive " << I8MaxLive << "\n" << "I16MaxLive " << I16MaxLive << "\n" << "I32MaxLive " << I32MaxLive << "\n" << "I64MaxLive " 
//			<< I64MaxLive << "\n" << "F32MaxLive " << F32MaxLive << "\n" << "F64MaxLive " << F64MaxLive << "\n\n";
	}
	unsigned LiveAnalyzer :: getMaxLiveCount(vector<Instruction*> Insts,Function *Callee,Type *Ty1,Type *Ty2)
	{
		// LiveValues - stores the Live values 
		vector<Value*> LiveValues;
		// Caller is a pointer to a Function instance and arg_
		for (Function::arg_iterator ai = Callee->arg_begin(),ae = Callee->arg_end(); ai != ae; ++ai)
		{
			Value *v = ai;
			if(v->getType() == Ty1 || v->getType() == Ty2)
				LiveValues.push_back(v);
		}
		//MaxCount - stores maximum Live element Count 
		unsigned MaxCount=0;	
		if(!Insts.empty())
		{	
			// BB is a pointer to a BasicBlock instance
			for (Function::iterator BB = Callee->begin(), BE = Callee->end(); --BE != BB || BE == BB; )
			{
				// The next statement works since operator<<(ostream&,...)
				// is overloaded for Instruction&
				//errs() << "Basic block (name=" << BE->getName() << ") has "
			      	//<< BE->size() << " instructions.\n";
			        //errs() << *BE <<"\n";
				// II is a pointer to a Instruction instance		
				for (BasicBlock::iterator II = BE->begin(), IE = BE->end(); --IE != II || IE == II; )
				{
					bool oflag = false;
					for(vector<Instruction*>::iterator VI = Insts.begin(),VE = Insts.end();
						VI != VE; ++VI)
					{
						Value *VecInst = *VI;
						Value *BBInst = IE;
						//errs() << **VI << "\t" << *IE << "\t";
						if(BBInst == VecInst)
						{
							oflag = true;
							break;
						}
						//errs() << oflag << "\n";
					}
//					errs() << "\n";
					if(oflag)
					{
						//for(unsigned i=0;i<59;++i)
						//errs() << IE->getOpcodeName(i) << "\n"; 
						bool flag = false;
						//OI is a pointer to a operands used in instruction
						for (User::op_iterator OI = IE->op_begin(), OE = IE->op_end(); OI!=OE;++OI)
						{
							for(unsigned a = 0; a < LiveValues.size(); ++a)
							{
								if(LiveValues[a] == *OI)
								{
									flag = true;
									break;
								}
							}
							if(!flag)
							{
								//errs() << "Operands :"<< (OI->get())<<"\t"<<*(OI->get())<< "\n\n";
								// If this operand is an argument it was not defined in the block.
								if (isa<Argument>(OI))
							     	{
						            	      	      LiveValues.push_back(*OI);
							      	}
				  				// Otherwize, it could be a constant value or ... 
								else if (!isa<Instruction>(OI))
								{
					            			continue; 
				        			}
				        			// Check if the parent of the instruction is not the block in question.
				        			else if (((Instruction*)OI)->getParent() != BE)
				        			{
										LiveValues.push_back(*OI);
								}
							}
						}
						for(unsigned a = 0; a < LiveValues.size(); ++a)
						{
//							errs() << *LiveValues[a] << "\n";
							if(LiveValues[a] == IE)
							{
								LiveValues.erase(LiveValues.begin()+a);
								break;
							}
						}
						unsigned size = LiveValues.size();
//						errs() << size << "\n";
						if(size > MaxCount)
							MaxCount = size;
					}
					if(IE==II)
						break;
				}
				if(BE==BB)
					break;
			}
		}
		return MaxCount;
	}
	unsigned LiveAnalyzer :: getLiveCount(Function *Callee) 
	{
		// LiveValues - stores the Live values 
		vector<Value*> LiveValues;
		//MaxCount - stores maximum Live element Count 
		unsigned MaxCount=0;
		// Caller is a pointer to a Function instance and arg_
		for (Function::arg_iterator ai = Callee->arg_begin(),ae = Callee->arg_end(); ai != ae; ++ai)
		{
			Value *v = ai;
			LiveValues.push_back(v);
		}
		// BB is a pointer to a BasicBlock instance
		for (Function::iterator BB = Callee->begin(), BE = Callee->end(); --BE != BB || BE == BB; )
		{
			// The next statement works since operator<<(ostream&,...)
			// is overloaded for Instruction&
			//errs() << "Basic block (name=" << BE->getName() << ") has "
		      	//<< BE->size() << " instructions.\n";
		        //errs() << *BE <<"\n";
			// II is a pointer to a Instruction instance		
			for (BasicBlock::iterator II = BE->begin(), IE = BE->end(); --IE != II || IE == II; )
			{
				//for(unsigned i=0;i<59;++i)
				//errs() << IE->getOpcodeName(i) << "\n"; 
				bool flag = false;
				//OI is a pointer to a operands used in instruction
				for (User::op_iterator OI = IE->op_begin(), OE = IE->op_end(); OI!=OE;++OI)
				{
					//errs() << "Operands :"<< (OI->get())<<"\t"<<*(OI->get())<< "\n\n";
					// If this operand is an argument it was not defined in the block.
					if (isa<Argument>(OI))
				     	{
						for(unsigned a = 0; a < LiveValues.size(); ++a)
						{
							if(LiveValues[a] == *OI)
							{
								flag = true;
								break;
							}
						}
						if(!flag)
	            	      	      			LiveValues.push_back(*OI);
				      	}
	  				// Otherwize, it could be a constant value or ... 
					else if (!isa<Instruction>(OI))
					{
	            				continue; 
	        			}
	        			// Check if the parent of the instruction is not the block in question.
	        			else if (((Instruction*)OI)->getParent() != BE)
	        			{
				  		for(unsigned a = 0; a < LiveValues.size(); ++a)
				  		{
							if(LiveValues[a] == *OI)
							{
								flag = true;
								break;
							}
						}
						if(!flag)	
							LiveValues.push_back(*OI);
					}
				}
				for(unsigned a = 0; a < LiveValues.size(); ++a)
				{
					if(LiveValues[a] == IE){
						LiveValues.erase(LiveValues.begin()+a);
						break;
					}
				}
				unsigned size = LiveValues.size();
				if(size > MaxCount)
					MaxCount = size;
				if(IE==II)
					break;
			}
			if(BE==BB)
				break;
		}
		return MaxCount;
	}	
}
