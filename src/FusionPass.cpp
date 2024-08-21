#include "llvm/ADT/SmallVector.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/IR/Dominators.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Support/raw_ostream.h"
#include <set>
#include <vector>

using namespace llvm;

namespace {

/*bool
instMightThrowException(const Instruction &I)
{
	if (isa<CallInst>(I) || isa<InvokeInst>(I))
	{
		if (Function *CalledFunc = I.getCalledFunction())
		{
			if (CalledFunc->isDeclaration())
			{
				if (!CalledFunc->hasFnAttribute(Attribute::NoUnwind))
				{
					return true;
				}
			}
			else
			{
				for (BasicBlock &BB : *CalledFunc)
				{
					for (Instruction &I : BB)
					{
						if (instMightThrowException(I))
						{
							return true;
						}
					}
				}
			}
		}
	}
	if (isa<LandingPadInst>(I))
	{
		return true;
	}
	return false;
}*/

bool
loopHasMultipleEntriesAndExits(const Loop &L)
{
	const BasicBlock *Header = L.getHeader();

	if (Header->getTerminator()->getNumSuccessors() > 2) return true;

	for (const BasicBlock *BB : L.blocks())
	{
		if (L.isLoopLatch(BB) || L.isLoopExiting(BB) || BB == Header)
		{
			continue;
		}
		for (const BasicBlock *Pred : predecessors(BB))
		{
			if (L.contains(Pred) == false)
			{
				return true;
			}
		}
		for (const BasicBlock *Succ : successors(BB))
		{
			if (L.contains(Succ) == false)
			{
				return true;
			}
		}
	}
	return false;
}

bool
loopMightThrowException(const Loop &L)
{
	for (const BasicBlock *BB : L.blocks())
	{
		for (const Instruction &I : *BB)
		{
			if (I.mayThrow())
			{
				return true;
			}
		}
	}
	return false;
}

bool
loopContainsVolatileInst(const Loop &L)
{
	for (const BasicBlock *BB : L.blocks())
	{
		for (const Instruction &I : *BB)
		{
			if (I.isVolatile())
			{
				return true;
			}
		}
	}
	return false;
}

bool
loopDominates(const Loop *L1, const Loop *L2, const DominatorTree &DT)
{
	const BasicBlock *H1 = L1->getLoopPreheader();
	const BasicBlock *H2 = L2->getLoopPreheader();
	return DT.properlyDominates(H1, H2);
}

bool
loopPostDominates(const Loop *L1, const Loop *L2, const PostDominatorTree &PDT)
{
	const BasicBlock *H1 = L1->getLoopPreheader();
	const BasicBlock *H2 = L2->getLoopPreheader();
	return PDT.properlyDominates(H1, H2);
}

bool
isControlFlowEqLoops(const Loop *L1, const Loop *L2, const DominatorTree &DT, const PostDominatorTree &PDT)
{
	return (loopDominates(L1, L2, DT) && loopPostDominates(L2, L1, PDT));
}

void
fuse(Loop *L1, Loop *L2)
{
	BasicBlock *Header1 = L1->getHeader(); /* Will be Header */
	BasicBlock *Header2 = L2->getHeader(); /* Will be deleted */
	BasicBlock *Latch1 = L1->getLoopLatch();
	BasicBlock *Latch2 = L2->getLoopLatch(); /* Will be Latch */
	BasicBlock *PreHeader1 = L1->getLoopPreheader();
	BasicBlock *PreHeader2 = L2->getLoopPreheader(); /* Will be deleted */
	
	BasicBlock *BodyEntry2 = Header2->getTerminator()->getSuccessor(0);
	BasicBlock *Exit2 = Header2->getTerminator()->getSuccessor(1);

	Instruction *Latch1Term = Latch1->getTerminator();
	if (Latch1Term->getOpcode() != Instruction::Br) throw std::exception();
	Latch1Term->replaceSuccessorWith(Header1, BodyEntry2);

	Instruction *Latch2Term = Latch2->getTerminator();
	if (Latch2Term->getOpcode() != Instruction::Br) throw std::exception();
	Latch2Term->replaceSuccessorWith(Header2, Header1);

	Instruction *Header1Term = Header1->getTerminator();
	Header1Term->replaceSuccessorWith(PreHeader2, Exit2);

	/* Update phis' predecessors */
	Header1->replacePhiUsesWith(Latch1, Latch2);
	Header2->replacePhiUsesWith(PreHeader2, PreHeader1);

	/* Move phis to Header1 */
	Instruction *FirstNonPhi1 = Header1->getFirstNonPHI();
	while (Header2->begin()->getOpcode() == Instruction::PHI)
	{
		Instruction *Phi = &*(Header2->begin());
		Phi->removeFromParent();
		Phi->insertBefore(FirstNonPhi1);
	}
	
	/* Cleanup */
	Latch1Term->setMetadata("llvm.loop", nullptr);

	PreHeader2->eraseFromParent();
	Header2->eraseFromParent();

	//assert(!L1->isInvalid() && "wtf have i done");
}

SmallVector<Loop *>
collectLoopsAtDepth(const LoopInfo &LI, unsigned Depth)
{
	SmallVector<Loop *> LoopsAtDepth;
	SmallVector<Loop *, 8> Worklist;
	for (Loop *TopLoop : LI)
	{
		Worklist.push_back(TopLoop);
		while (!Worklist.empty())
		{
			Loop *L = Worklist.pop_back_val();
			if (L->getLoopDepth() == Depth)
			{
				LoopsAtDepth.push_back(L);
			}
			else
			{
				for (Loop *SubLoop : *L)
				{
					Worklist.push_back(SubLoop);
				}
			}
		}
	}
	return LoopsAtDepth;
}

bool
processLoops(SmallVector<Loop *> &Loops, DominatorTree &DT, PostDominatorTree &PDT, DenseMap<const BasicBlock *, const SCEV *> &LoopSCEVInfo)
{
	/* Collect candidates */
	std::set<Loop *> Candidates;
	for (Loop *L : Loops)
	{
		if	(
			L->isLoopSimplifyForm()
			&& loopContainsVolatileInst(*L) == false
			//&& loopMightThrowException(*L) == false /* Somehow always returns true */
			&& loopHasMultipleEntriesAndExits(*L) == false
			)
		{
			Candidates.insert(L);
		}
	}

	/* Build Control Flow Equivalent sets */
	std::vector<std::vector<Loop *>> CFEs;
	for (Loop *L : Candidates)
	{
		CFEs.push_back(std::vector<Loop *> {L});
	}
	for (auto it1 = CFEs.begin(), it1e = CFEs.end(); it1 != it1e; ++it1)
	{
		Loop *L1 = (*it1)[0];
		
		for (auto it2 = Candidates.begin(), it2e = Candidates.end(); it2 != it2e;)
		{
			Loop *L2 = *it2;
			if (isControlFlowEqLoops(L1, L2, DT, PDT))
			{
				//outs() << "	yes\n";
				it1->push_back(L2);
				it2 = Candidates.erase(it2);
			}
			else
			{
				++it2;
			}
		}
	}
	CFEs.erase(
		std::remove_if(
			CFEs.begin(),
			CFEs.end(),
			[](const std::vector<Loop *> &v)
			{
				return v.size() == 1;
			}
		),
		CFEs.end()
	);
	//outs() << CFEs.size() << "__\n";

	bool fused = false;
	for (auto &set : CFEs)
	{
		for (auto it1 = set.begin(), it1e = set.end(); it1 != it1e; ++it1)
		{
			Loop *L1 = *it1;
			for (auto it2 = std::next(it1), it2e = set.end(); it2 != it2e; ++it2)
			{
				Loop *L2 = *it2;
				const auto TripCount1 = LoopSCEVInfo.at(L1->getHeader());
				const auto TripCount2 = LoopSCEVInfo.at(L2->getHeader());
				if (TripCount1->getSCEVType() == SCEVTypes::scCouldNotCompute ||
					TripCount2->getSCEVType() == SCEVTypes::scCouldNotCompute)
				{
					outs() << "cncompute\n";
					continue;
				}
				if (TripCount1 != TripCount2)
				{
					//TripCount1->print(outs());
					//outs() << "\n";
					continue;
				}

				SmallVector<BasicBlock *> Successors;
				L1->getExitBlocks(Successors);
				outs() << "size: " << Successors.size() << "\n";
				for (const BasicBlock *BB : Successors)
				{
					if (BB != L2->getLoopPreheader())
					{
						outs() << "not adj\n";
						//continue
					}
				}

				fuse(L1, L2);
				fused = true;
				return fused;
			}
		}
	}
	return fused;
}

DenseMap<const BasicBlock *, const SCEV *>
getLoopSCEVInfo(const LoopInfo &LI, ScalarEvolution &SE)
{
	DenseMap<const BasicBlock *, const SCEV *> LoopSCEVInfo;

	const SmallVector<Loop *> Loops = LI.getLoopsInPreorder();
	for (const Loop *L : Loops)
	{
		LoopSCEVInfo.insert(std::make_pair(L->getHeader(), SE.getSymbolicMaxBackedgeTakenCount(L)));
	}
	return LoopSCEVInfo;
}

bool
FuseLoops(Function &F, FunctionAnalysisManager &FAM)
{
	bool FusedAny = false;
	outs() << "Func: " << F.getName() << "\n";

	/* Get analyses */
	LoopInfo          &LI  = FAM.getResult<LoopAnalysis>(F);
	DominatorTree     &DT  = FAM.getResult<DominatorTreeAnalysis>(F);
	PostDominatorTree &PDT = FAM.getResult<PostDominatorTreeAnalysis>(F);
	ScalarEvolution   &SE  = FAM.getResult<ScalarEvolutionAnalysis>(F);

	/* Store important Scalar Evolution info in map<Header *, SCEV *> */
	auto LoopSCEVInfo = getLoopSCEVInfo(LI, SE);

	SmallVector<Loop *> LoopsToProcess;
	for (unsigned i = 1; (LoopsToProcess = collectLoopsAtDepth(LI, i)).empty() == false; i++)
	{
		outs() << "loop count before: " << LI.getTopLevelLoops().size() << "\n";
		FusedAny = processLoops(LoopsToProcess, DT, PDT, LoopSCEVInfo);
		if (FusedAny)
		{
			DT = DominatorTree(F);
			PDT = PostDominatorTree(F);
			LI = LoopInfo(DT);
		}
		outs()	<< "loop count after: "
			<< LI.getTopLevelLoops().size() << "\n";
		break;
	}
	return FusedAny;
}

struct FusionPass : PassInfoMixin<FusionPass> 
{
	PreservedAnalyses 
	run(Function &F, FunctionAnalysisManager &AnalysisManager) 
	{
		bool changed = FuseLoops(F, AnalysisManager);
		return changed ? PreservedAnalyses::none() : PreservedAnalyses::all();
	}

	static bool 
	isRequired(void) 
	{ 
		return (true); 
	}
};
} /* namespace */

void
CallBackForPassBuilder(PassBuilder &PB)
{
	PB.registerPipelineParsingCallback(
		(	[](
			StringRef Name,
			FunctionPassManager &FPM,
			ArrayRef<PassBuilder::PipelineElement>
			) -> bool
			{
				if (Name == "fusion-pass")
				{
					FPM.addPass(FusionPass());
					return (true);
				}
				else
				{
					return (false);
				}
			}
		)
	);
} /* CallBackForPassBuider */

PassPluginLibraryInfo 
getFusionPassPluginInfo(void)
{
	uint32_t     APIversion =  LLVM_PLUGIN_API_VERSION;
	const char * PluginName =  "fusion-pass";
	const char * PluginVersion =  LLVM_VERSION_STRING;
    
	PassPluginLibraryInfo info = 
	{ 
		APIversion, 
		PluginName, 
		PluginVersion, 
		CallBackForPassBuilder
	};

	return (info);
} /* getFusionPassPluginInfo */

extern "C" LLVM_ATTRIBUTE_WEAK ::llvm::PassPluginLibraryInfo
llvmGetPassPluginInfo() 
{
	return (getFusionPassPluginInfo());
} /* llvmGetPassPluginInfo */
