#include "llvm/ADT/SmallVector.h"
#include "llvm/Analysis/AssumptionCache.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/DependenceAnalysis.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/TargetTransformInfo.h"
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
	if (!L.getExitBlock()) return true;

	for (const BasicBlock *BB : L.blocks())
	{
		if (L.isLoopExiting(BB) || BB == Header)
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

Instruction *
blockProducesValue(BasicBlock *BB, const Value *V)
{
	for (Instruction &I : *BB)
	{
		if (&I == V)
		{
			return &I;
		}
	}
	return nullptr;
}

bool
blockUsesValue(const BasicBlock *BB, const Value *V)
{
	for (const Instruction &I : *BB)
	{
		for (const Value *OP : I.operands())
		{
			if (OP == V)
			{
				return true;
			}
		}
	}
	return false;
}

void
fuse(Loop *L1, Loop *L2)
{
	BasicBlock *Header1 = L1->getHeader(); /* Will be Header */
	BasicBlock *Header2 = L2->getHeader(); /* Will be deleted */
	BasicBlock *Latch1 = L1->getLoopLatch(); /* Will be Latch */
	BasicBlock *Latch2 = L2->getLoopLatch();
	BasicBlock *PreHeader1 = L1->getLoopPreheader();
	BasicBlock *PreHeader2 = L2->getLoopPreheader(); /* Will be deleted */	

	BasicBlock *BodyEntry2 = Header2->getTerminator()->getSuccessor(0);
	BasicBlock *Exit2 = Header2->getTerminator()->getSuccessor(1);

	assert(PreHeader2->size() == 1 && "Incorrect PreHeader size");

	while (pred_begin(Latch1) != pred_end(Latch1))
	{
		(*(pred_begin(Latch1)))->getTerminator()->replaceSuccessorWith(Latch1, BodyEntry2);
	}

	/*while (pred_begin(Latch2) != pred_end(Latch2))
	{
		(*(pred_begin(Latch2)))->getTerminator()->replaceSuccessorWith(Latch2, Latch1);
	}*/
	Latch1->moveAfter(Latch2);
	Instruction *Latch2Term = Latch2->getTerminator();
	Latch2Term->replaceSuccessorWith(Header2, Latch1);

	Instruction *Header1Term = Header1->getTerminator();
	Header1Term->replaceSuccessorWith(PreHeader2, Exit2);

	/* Update phis' predecessors */
	//Header2->replacePhiUsesWith(Latch2, Latch1);
	Header2->replacePhiUsesWith(PreHeader2, PreHeader1);
	//SmallVector<Instruction *> ToDelete;
	/*if (false){
	for (auto it = Header2->begin(); it != Header2->getFirstNonPHIIt();)
	{
		PHINode *Phi = dyn_cast<PHINode>(&*it);
		const Value *V = Phi->getIncomingValueForBlock(Latch2);
		Instruction *I;
		if (I = blockContainsValue(Latch2, V))
		{
			outs() << "useless\n";
			I->eraseFromParent();
			Phi->eraseFromParent();
			//Phi->removeIncomingValue(Latch2);
			//Phi->setIncomingValueForBlock(Latch2, Phi->getIncomingValue(0));
			//outs() << Phi->hasConstantValue() << "\n";
		}
		else ++it;
	}}*/
	//for (Instruction *I : ToDelete)
	//{
	//	I->removeFromParent();
	//}
	Header2->replacePhiUsesWith(Latch2, Latch1);

	/* Move phis to Header1 */
	Instruction *FirstNonPhi1 = Header1->getFirstNonPHI();
	while (Header2->begin()->getOpcode() == Instruction::PHI)
	{
		Instruction *Phi = &*(Header2->begin());
		Phi->removeFromParent();
		Phi->insertBefore(FirstNonPhi1);
	}
	assert(Header2->size() == 2);
	
	/* Cleanup */
	Latch2Term->setMetadata("llvm.loop", nullptr);

	PreHeader2->eraseFromParent();
	Header2->eraseFromParent();
	//Latch2->eraseFromParent();
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
tryInsertInCFESet(std::list<Loop *> &set, Loop *L, const DominatorTree &DT, const PostDominatorTree &PDT)
{
	if (set.empty())
	{
		return false;
	}

	for (auto it = set.begin(); it != set.end(); ++it)
	{
		if (it == set.begin() && isControlFlowEqLoops(L, *it, DT, PDT))
		{
			set.insert(it, L);
			return true;
		}

		auto nit = std::next(it);
		if (nit != set.end() 
			&& isControlFlowEqLoops(*it, L, DT, PDT) && isControlFlowEqLoops(L, *nit, DT, PDT))
		{
			set.insert(nit, L);
			return true;
		}

		if (nit == set.end() && isControlFlowEqLoops(*it, L, DT, PDT))
		{
			set.push_back(L);
			return true;
		}
	}
	return false;
}

std::list<std::list<Loop *>>
buildCFESets(const std::set<Loop *> &Candidates, const DominatorTree &DT, const PostDominatorTree &PDT)
{
	std::list<std::list<Loop *>> CFEs;

	for (Loop *L : Candidates)
	{
		bool inserted = false;
		for (auto &set : CFEs)
		{
			if (tryInsertInCFESet(set, L, DT, PDT))
			{
				inserted = true;
				break;
			}
		}

		if (inserted == false)
		{
			CFEs.push_back(std::list<Loop *> {L});
		}
	}

	/* Delete sets with only one loop */
	CFEs.erase(
		std::remove_if(
			CFEs.begin(),
			CFEs.end(),
			[](const std::list<Loop *> &set)
			{
				return set.size() == 1;
			}
		),
		CFEs.end()
	);

	return CFEs;
}

bool
blocksHaveNegativeDependencies(const BasicBlock &First, const BasicBlock &Second)
{
	for (const Instruction &I1 : First)
	{
		if (blockUsesValue(&Second, &I1))
		{
			return true;
		}
	}
	return false;
}

bool
loopsHaveInvalidDependencies(const Loop *L1, const Loop *L2)
{
	for (BasicBlock *BB1 : L1->blocks())
	{
		for (BasicBlock *BB2 : L2->blocks())
		{
			if (blocksHaveNegativeDependencies(*BB1, *BB2))
			{
				return true;
			}
		}
	}
	return false;
}

bool
areLoopsAdjacent(const Loop *L1, const Loop *L2)
{
	if (L2->getLoopPreheader()->size() > 1) 
	{
		return false;
	}

	BasicBlock *Exit1 = L1->getExitBlock();
	if (!Exit1 || Exit1->size() > 1)
	{
		return false;
	}

	if (Exit1 != L2->getLoopPreheader())
	{
		return false;
	}
	return true;
}

bool
tryMoveInterferingInstructions(Loop *L1, Loop *L2)
{
	DenseMap<BasicBlock *, int> WaysToMove; /* 10 - up; 01 - down; 11 both; 00 - can't move */
	BasicBlock *Exit = L1->getExitBlock();
	BasicBlock *BB = Exit->getSingleSuccessor();
	while (BB != L2->getLoopPreheader())
	{
		WaysToMove.insert(std::make_pair(BB, 0b11));

		for (BasicBlock *L1BB : L1->blocks())
		{
			for (Instruction &L1I : *L1BB)
			{
				if (blockUsesValue(BB, &L1I))
				{
					WaysToMove[BB] &= 0b01;
				}
			}
		}
		for (BasicBlock *L2BB : L2->blocks())
		{
			for (Instruction &I : *BB)
			{
				if (blockUsesValue(L2BB, &I))
				{
					WaysToMove[BB] &= 0b10;
				}
			}
		}
		if (WaysToMove.at(BB) == 0b00)
		{
			return false;
		}
		BB = BB->getSingleSuccessor();
	}

	BasicBlock *PreHeader1 = L1->getLoopPreheader();
	for (auto &pair : WaysToMove)
	{
		BasicBlock *BBToMove = pair.first;
		if (pair.second & 0b10)
		{
			while (pred_begin(BBToMove) != pred_end(BBToMove))
			{
				(*(pred_begin(BBToMove)))->getTerminator()->replaceSuccessorWith(BBToMove, BBToMove->getSingleSuccessor());
			}
			while (pred_begin(PreHeader1) != pred_end(PreHeader1))
			{
				(*(pred_begin(PreHeader1)))->getTerminator()->replaceSuccessorWith(PreHeader1, BBToMove);
			}
			BBToMove->getTerminator()->replaceSuccessorWith(BBToMove->getSingleSuccessor(), PreHeader1);
		}
	}
	return true;
}

bool
tryCleanPreHeader(Loop *L1, Loop *L2)
{
	DenseMap<Instruction *, int> WaysToMove;

	BasicBlock *Exit1 = L1->getExitBlock();
	BasicBlock *PreHeader2 = L2->getLoopPreheader();
	if (Exit1 != PreHeader2) assert(Exit1->size() == 1 && Exit1->getSingleSuccessor() == PreHeader2);

	for (Instruction &I : *PreHeader2)
	{
		if (&I == PreHeader2->getTerminator())
		{
			break;
		}
		WaysToMove.insert(std::make_pair(&I, 0b11));
		for (BasicBlock *L1BB : L1->blocks())
		{
			for (Value *V : I.operands())
			{
				if (blockProducesValue(L1BB, V))
				{
					WaysToMove[&I] &= 0b01;
				}
			}
		}

		for (BasicBlock *L2BB : L2->blocks())
		{
			if (blockUsesValue(L2BB, &I))
			{
				WaysToMove[&I] &= 0b10;
			}
		}
		if (WaysToMove.at(&I) == 0b00)
		{
			return false;
		}
	}

	BasicBlock *PreHeader1 = L1->getLoopPreheader();
	Instruction *PreHeader1Term = PreHeader1->getTerminator();
	int move = 0b11;
	for (auto &pair : WaysToMove)
	{
		move &= pair.second;
	}
	/*for (auto &pair : WaysToMove)
	{
		Instruction *I = pair.first;
		//int move = pair.second;
		
		if (move & 0b10)
		{
			I->moveBefore(PreHeader1Term);
		}
		else
		{
			I->moveBefore(&*(L2->getExitBlock()->begin()));
		}
	}*/
	if (move & 0b10)
	{
		while (&*(PreHeader2->begin()) != PreHeader2->getTerminator())
		{
			(&*(PreHeader2->begin()))->moveBefore(PreHeader1Term);
		}
	}
	else if (move & 0b01)
	{
		Instruction *Exit2Start = &*(L2->getExitBlock()->begin());
		while (&*(PreHeader2->begin()) != PreHeader2->getTerminator())
		{
			(&*(PreHeader2->begin()))->moveBefore(Exit2Start);
		}
	}
	else
	{
		return false;
	}
	assert(PreHeader2->size() == 1 && "Incorrect PreHeader cleaning");
	return true;
}

bool
tryCleanExit(Loop *L1, Loop *L2)
{
	BasicBlock *Exit1 = L1->getExitBlock();
	BasicBlock *PreHeader2 = L2->getLoopPreheader();
	if (Exit1 == PreHeader2)
	{
		return true;
	}

	assert(Exit1->getSingleSuccessor() == PreHeader2);

	while (&*(Exit1->begin()) != Exit1->getTerminator())
	{
		(&*(Exit1->begin()))->moveBefore(&*(PreHeader2->begin()));
	}
	/* For now always returns true */
	return true;
}

bool
tryCleanExitAndPreHeader(Loop *L1, Loop *L2)
{
	return tryCleanExit(L1, L2) && tryCleanPreHeader(L1, L2);
}

bool
tryMakeLoopsAdjacent(Loop *L1, Loop *L2)
{
	if (areLoopsAdjacent(L1, L2))
	{
		return true;
	}
	//return false;

	BasicBlock *Exit = L1->getExitBlock();
	if (Exit == nullptr) return false;

	BasicBlock *PreHeader2 = L2->getLoopPreheader();
	//outs() << "\tpre size: " << PreHeader2->size() << "\n";
	if (Exit->size() > 1 || PreHeader2->size() > 1)
	{
		if (tryCleanExitAndPreHeader(L1, L2) == false)
		{
			outs() << "can not clean pre header\n";
			return false;
		}
	}

	if (Exit->getSingleSuccessor() == PreHeader2)
	{
		while (pred_begin(Exit) != pred_end(Exit))
		{
			(*(pred_begin(Exit)))->getTerminator()->replaceSuccessorWith(Exit, PreHeader2);
		}
		Exit->eraseFromParent();
	}
	if (L1->getExitBlock() == L2->getLoopPreheader() && L2->getLoopPreheader()->size() == 1)
	{
		return true;
	}

	//outs() << "can not make adj\n";
	return false;
	return tryMoveInterferingInstructions(L1, L2);
}

bool
processSet(std::list<Loop *> &set, const DenseMap<const BasicBlock *, const SCEV *> &LoopSCEVInfo)
{
	for (auto it1 = set.begin(), it1e = set.end(); it1 != it1e; ++it1)
	{
		Loop *L1 = *it1;
		for (auto it2 = std::next(it1), it2e = set.end(); it2 != it2e; ++it2)
		{
			Loop *L2 = *it2;
			const SCEV *TripCount1 = LoopSCEVInfo.at(L1->getHeader());
			const SCEV *TripCount2 = LoopSCEVInfo.at(L2->getHeader());
			if (TripCount1->getSCEVType() == SCEVTypes::scCouldNotCompute ||
				TripCount2->getSCEVType() == SCEVTypes::scCouldNotCompute)
			{
				outs() << "cncompute\n";
				continue;
			}
			if (TripCount1 != TripCount2)
			{
				continue;
			}
			if (false &&loopsHaveInvalidDependencies(L1, L2))
			{
				continue;
			}
			if (tryMakeLoopsAdjacent(L1, L2) == false)
			{
				continue;
			}
			/* Finally, fuse loops */
			fuse(L1, L2);
			return true;
		}
	}
	return false;
}

bool
processLoops(const SmallVector<Loop *> &Loops, const DominatorTree &DT, const PostDominatorTree &PDT, const DenseMap<const BasicBlock *, const SCEV *> &LoopSCEVInfo)
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
	std::list<std::list<Loop *>> CFEs = buildCFESets(Candidates, DT, PDT);

	/* Try to fuse any loops from sets */
	bool fused = false;
	for (auto &set : CFEs)
	{
		fused |= processSet(set, LoopSCEVInfo);
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
	//DependenceInfo    &DI  = FAM.getResult<DependenceAnalysis>(F);
	//TargetLibraryInfo &TLI = FAM.getResult<TargetLibraryAnalysis>(F);
	//AssumptionCache   &AC  = FAM.getResult<AssumptionAnalysis>(F);
	//AAResults	  &AA  = FAM.getResult<AliasAnalysis>(F);
	ScalarEvolution   &SE  = FAM.getResult<ScalarEvolutionAnalysis>(F);

	/* Store important Scalar Evolution info in map<Header *, SCEV *> */
	auto LoopSCEVInfo = getLoopSCEVInfo(LI, SE);
	outs() << "\tloop count before: " << LI.getLoopsInPreorder().size() << "\n";
	SmallVector<Loop *> LoopsToProcess;
	for (unsigned i = 1; (LoopsToProcess = collectLoopsAtDepth(LI, i)).empty() == false;)
	{
		FusedAny = processLoops(LoopsToProcess, DT, PDT, LoopSCEVInfo);
		if (FusedAny)
		{
			/* Recalculate analyses since CFG changed */
			DT  = DominatorTree(F);
			PDT = PostDominatorTree(F);
			LI  = LoopInfo(DT);
		}
		else
		{
			i++;
		}
	}
	outs()	<< "\tloop count after: "
		<< LI.getLoopsInPreorder().size() << "\n";
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
	uint32_t    APIversion    = LLVM_PLUGIN_API_VERSION;
	const char *PluginName    = "fusion-pass";
	const char *PluginVersion = LLVM_VERSION_STRING;
    
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
