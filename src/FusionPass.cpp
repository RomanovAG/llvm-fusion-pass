#include "llvm/Analysis/DependenceAnalysis.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;

namespace {

/* -debug flag handler */
cl::opt<bool> DebugMode(
    "debug", cl::desc("Enable debug mode for fusion-pass"),
    cl::init(false));

bool
loopHasMultipleEntriesAndExits(const Loop &L)
{
	const BasicBlock *Header = L.getHeader();

	if (Header->getTerminator()->getNumSuccessors() > 2) return true;
	if (!L.getExitingBlock()) return true;
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
} /* loopHasMultipleEntriesAndExits */

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
} /* loopMightThrowException */

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
} /* loopContainsVolatileInst */

bool
loopDominates(const Loop *L1, const Loop *L2, const DominatorTree &DT)
{
	const BasicBlock *H1 = L1->getLoopPreheader();
	const BasicBlock *H2 = L2->getLoopPreheader();
	return DT.properlyDominates(H1, H2);
} /* loopDominates */

bool
loopPostDominates(const Loop *L1, const Loop *L2, const PostDominatorTree &PDT)
{
	const BasicBlock *H1 = L1->getLoopPreheader();
	const BasicBlock *H2 = L2->getLoopPreheader();
	return PDT.properlyDominates(H1, H2);
} /* loopPostDominates */

bool
isControlFlowEqLoops(const Loop *L1, const Loop *L2, const DominatorTree &DT, const PostDominatorTree &PDT)
{
	return (loopDominates(L1, L2, DT) && loopPostDominates(L2, L1, PDT));
} /* isControlFlowEqLoops */

void
replaceVariableInBlock(BasicBlock &BB, Value *OldValue, Value *NewValue)
{
	for (Instruction &I : BB)
	{
		for (Use &U : I.operands())
		{
			if (U.get() == OldValue) 
			{
				U.set(NewValue);
			}
		}
	}
} /* replaceVariableInBlock */

void
replaceVariableInLoop(Loop &L, Value *OldValue, Value *NewValue)
{
	for (BasicBlock *BB : L.blocks())
	{
		replaceVariableInBlock(*BB, OldValue, NewValue);
	}
} /* replaceVariableInLoop */

void
replaceVariableInFunction(Function &F, Value *OldValue, Value *NewValue)
{
	for (BasicBlock &BB : F)
	{
		replaceVariableInBlock(BB, OldValue, NewValue);
	}
} /* replaceVariableInFunction */

bool
isIndex(const BasicBlock &BB, const Value &V)
{
	for (auto it1 = BB.begin(), it2 = std::next(it1); it2 != BB.end(); ++it1, ++it2)
	{
		if (&*it2 == BB.getTerminator())
		{
			if (it1->getOpcode() == Instruction::ICmp && it1->getOperand(0) == &V)
			{
				if (it2->getOperand(0) == &*it1)
				{
					return true;
				}
			}
		}
	}
	return false;
} /* isIndex */

Value *
getIndex(const BasicBlock &Header)
{
	for (auto it1 = Header.begin(), it2 = std::next(it1); it2 != Header.end(); ++it1, ++it2)
	{
		if (&*it2 == Header.getTerminator())
		{
			if (it1->getOpcode() == Instruction::ICmp &&  it2->getOperand(0) == &*it1)
			{
				return it1->getOperand(0);
			}
		}
	}
	return nullptr;
} /* getIndex */

void
fuse(Loop *L1, Loop *L2)
{
	BasicBlock *Header1 = L1->getHeader(); /* Will be Header */
	BasicBlock *Header2 = L2->getHeader(); /* Will be deleted */
	BasicBlock *Latch1 = L1->getLoopLatch(); /* Will be Latch */
	BasicBlock *Latch2 = L2->getLoopLatch(); /* Will be deleted */  
	BasicBlock *PreHeader1 = L1->getLoopPreheader();
	BasicBlock *PreHeader2 = L2->getLoopPreheader(); /* Will be deleted */	

	assert(Latch1->size() == Latch2->size());

	BasicBlock *BodyEntry2 = Header2->getTerminator()->getSuccessor(0);
	BasicBlock *Exit2 = Header2->getTerminator()->getSuccessor(1);

	assert(PreHeader2->size() == 1 && "Incorrect PreHeader2 size");

	/* Unlink Latch1 from first loop and move it after Latch2 */
	while (pred_begin(Latch1) != pred_end(Latch1))
	{
		(*(pred_begin(Latch1)))->getTerminator()->replaceSuccessorWith(Latch1, BodyEntry2);
	}

	Latch1->moveAfter(Latch2);
	Instruction *Latch2Term = Latch2->getTerminator();
	Latch2Term->replaceSuccessorWith(Header2, Latch1);

	/* Since PreHeader2 consists only of one branch instruction, no need to preserve it */
	Instruction *Header1Term = Header1->getTerminator();
	Header1Term->replaceSuccessorWith(PreHeader2, Exit2);

	/* Update phis' values */
	Function *F = Header1->getParent();
	SmallVector<PHINode *> PhiToDelete;
	for (PHINode &Phi2 : Header2->phis())
	{
		Value *OldValue = &Phi2;
		if (isIndex(*Header2, Phi2))
		{
			Value *NewValue = getIndex(*Header1);

			replaceVariableInFunction(*F, OldValue, NewValue);
			PhiToDelete.push_back(&Phi2);
		}
		else
		{
			for (PHINode &Phi1 : Header1->phis())
			{
				if (&Phi1 == Phi2.getIncomingValue(0))
				{
					Value *NewValue = Phi1.getIncomingValueForBlock(Latch1);
					Phi1.setIncomingValueForBlock(Latch1, Phi2.getIncomingValueForBlock(Latch2));

					/* Update local scope first */
					replaceVariableInLoop(*L2, OldValue, NewValue);

					/* Update global scope */
					replaceVariableInFunction(*F, OldValue, &Phi1);
					PhiToDelete.push_back(&Phi2);
				}
			}
		}
	}
	for (PHINode *Phi : PhiToDelete)
	{
		Phi->eraseFromParent();
	}

	Header2->replacePhiUsesWith(PreHeader2, PreHeader1);
	Header2->replacePhiUsesWith(Latch2, Latch1);

	/* Move phis to Header1 */
	Instruction *FirstNonPhi1 = Header1->getFirstNonPHI();
	while (Header2->begin()->getOpcode() == Instruction::PHI)
	{
		Instruction *Phi = &*(Header2->begin());
		Phi->removeFromParent();
		Phi->insertBefore(FirstNonPhi1);
	}

	assert(Header2->size() == 2 && "Incorrect Header2 size");
	
	while (pred_begin(Latch2) != pred_end(Latch2))
	{
		(*(pred_begin(Latch2)))->getTerminator()->replaceSuccessorWith(Latch2, Latch1);
	}
	
	/* Cleanup */
	PreHeader2->eraseFromParent();
	Header2->eraseFromParent();
	Latch2->eraseFromParent();
} /* fuse */

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
} /* collectLoopsAtDepth */

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
} /* tryInsertInCFESet */

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
} /* buildCFESets */

bool
blockProducesValue(BasicBlock *BB, const Value *V)
{
	for (Instruction &I : *BB)
	{
		if (&I == V)
		{
			return true;
		}
	}
	return false;
} /* blockProducesValue */

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
} /* blockUsesValue */

/* Deprecated */
/*bool
blocksHaveNegativeDependencies(const BasicBlock &First, const BasicBlock &Second)
{
	for (const Instruction &I1 : First)
	{
		if (I1.getOpcode() == Instruction::Store)
		{
			for (Value *V : I1.operands())
			{
				if (blockUsesValue(&Second, V))
				{
					return true;
				}
			}
		}
		if (blockUsesValue(&Second, &I1))
		{
			return true;
		}
	}
	return false;
}*/

bool
refersToIndex(const Instruction &I)
{
	assert(I.getOpcode() == Instruction::GetElementPtr);
	bool AllIndex = true;

	for (Value *V : I.operands())
	{
		if (isa<Constant>(V) || isa<Argument>(V))
		{
			//errs() << I.getNumOperands() <<" const\n";
			continue;
		}

		Instruction *II = dyn_cast<Instruction>(V);
		if (!II)
		{
			return false;
		}
		else if (II->getOpcode() == Instruction::SExt || II->getOpcode() == Instruction::ZExt)
		{
			II = dyn_cast<Instruction>(II->getOperand(0));
			if (II && II->getOpcode() == Instruction::PHI)
			{
				AllIndex &= isIndex(*(II->getParent()), *II);
			}
			else
			{
				//errs() << "f1\n";
				return false;
			}
		}
		else if (II->getOpcode() == Instruction::GetElementPtr)
		{
			AllIndex &= refersToIndex(*II);
		}
		else if (II->getOpcode() == Instruction::PHI)
		{
			AllIndex &= isIndex(*(II->getParent()), *II);
		}
		else
		{	
			//errs() << II->getOpcodeName() <<" f2\n";
			return false;
		}
	}
	return AllIndex;
} /* refersToIndex */

bool
areSameIndex(const Instruction &I1, const Instruction &I2)
{
	assert(I1.getOpcode() == Instruction::GetElementPtr && I2.getOpcode() == Instruction::GetElementPtr);

	/* For both GEP instructions check if they refer to unmodified loop index */
	return refersToIndex(I1) && refersToIndex(I2);
} /* areSameIndex */

bool
blocksHaveFlowDependencies(BasicBlock &BB1, BasicBlock &BB2, DependenceInfo &DI)
{
	for (Instruction &I1 : BB1)
	{
		for (Instruction &I2 : BB2)
		{
			if (const auto Dep = DI.depends(&I1, &I2, true))
			{
				if (Dep->isFlow())
				{
					return true;
				}
			}
		}
	}
	return false;
} /* blocksHaveFlowDependencies */

bool
loopsHaveInvalidDependencies(const Loop *L1, const Loop *L2, DependenceInfo &DI)
{
	/* For now only simple flow is allowed (array access at unmodified loop index) */
	for (BasicBlock *BB1 : L1->blocks())
	{
		for (Instruction &I1 : *BB1)
		{
			for (BasicBlock *BB2 : L2->blocks())
			{
				for (Instruction &I2 : *BB2)
				{
					if (const auto Dep = DI.depends(&I1, &I2, true))
					{
						if (Dep->isFlow())
						{
							//errs() << "Entereddep\n";
							//errs() << Dep->getSrc()->getOpcodeName() << " ";
							//errs() << Dep->getDst()->getOpcodeName() << "\n";
							Instruction *Src, *Dst;
							if ((Src = dyn_cast<Instruction>(Dep->getSrc()->getOperand(1))) && (Dst = dyn_cast<Instruction>(Dep->getDst()->getOperand(0))))
							{
								if (Src->getOpcode() == Instruction::GetElementPtr && Dst->getOpcode() == Instruction::GetElementPtr)
								{
									//errs() << "test same index: ";
									if (areSameIndex(*Src, *Dst))
									{
										//errs() << "a[i]\n";
										continue;
									}
								}
							}
							//errs() << "inv dep\n";
							return true;
						}
					}
				}
			}
		}
	}
	return false;
} /* loopsHaveInvalidDependencies */

bool
areLoopsAdjacent(const Loop *L1, const Loop *L2)
{
	BasicBlock *Exit1 = L1->getExitBlock();
	assert(Exit1 && "Loop 1 has no exit block");
	if (Exit1 != L2->getLoopPreheader())
	{
		return false;
	}
	
	if (Exit1->size() > 1)
	{
		return false;
	}
	return true;
} /* areLoopsAdjacent */

bool
tryMoveInterferingCode(Loop *L1, Loop *L2, DependenceInfo &DI)
{
	DenseMap<BasicBlock *, int> WaysToMove; /* 10 - up; 01 - down; 11 both; 00 - can't move */
	BasicBlock *Exit1 = L1->getExitBlock();
	BasicBlock *PreHeader2 = L2->getLoopPreheader();
	BasicBlock *BB = Exit1->getSingleSuccessor();

	assert(Exit1 != PreHeader2 
		&& Exit1->getSingleSuccessor() != PreHeader2 
		&& "No complex interfering code here");
	return false;

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
} /* tryMoveInterferingCode */

bool
tryCleanPreHeader(Loop *L1, Loop *L2, DependenceInfo &DI)
{
	DenseMap<Instruction *, int> WaysToMove; /* 10 - up; 01 - down; 11 both; 00 - can't move */

	BasicBlock *Exit1 = L1->getExitBlock();
	BasicBlock *PreHeader2 = L2->getLoopPreheader();
	if (Exit1 != PreHeader2) assert(Exit1->size() == 1 && Exit1->getSingleSuccessor() == PreHeader2);

	int m = 0b11;
	for (BasicBlock *BB1 : L1->blocks())
	{
		if (blocksHaveFlowDependencies(*BB1, *PreHeader2, DI))
		{
			m &= 0b01;
		}
	}
	for (BasicBlock *BB2 : L2->blocks())
	{
		if (blocksHaveFlowDependencies(*PreHeader2, *BB2, DI))
		{
			m &= 0b10;
		}
	}
	if (m == 0) {errs() << "flow\n"; return false;}

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

	/* Move entire set of instructions up or down */
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
} /* tryCleanPreHeader */

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
} /* tryCleanExit */

bool
tryCleanExitAndPreHeader(Loop *L1, Loop *L2, DependenceInfo &DI)
{
	return tryCleanExit(L1, L2) && tryCleanPreHeader(L1, L2, DI);
} /* tryCleanExitAndPreHeader */

bool
tryMakeLoopsAdjacent(Loop *L1, Loop *L2, DependenceInfo &DI)
{
	if (areLoopsAdjacent(L1, L2))
	{
		return true;
	}

	BasicBlock *Exit1 = L1->getExitBlock();
	BasicBlock *PreHeader2 = L2->getLoopPreheader();

	/* Check if loops have more than 2 control-flow equivalent Basic Blocks between them */
	if (Exit1 != PreHeader2 && Exit1->getSingleSuccessor() != PreHeader2)
	{
		if (tryMoveInterferingCode(L1, L2, DI) == false)
		{
			return false;
		}
	}

	/* Remove important instructions from BB between loops if possible */
	if (Exit1->size() > 1 || PreHeader2->size() > 1)
	{
		if (tryCleanExitAndPreHeader(L1, L2, DI) == false)
		{
			//errs() << "can not clean pre header\n";
			return false;
		}
	}

	/* Combine Exit and PreHeader into one BB */
	if (Exit1->getSingleSuccessor() == PreHeader2)
	{
		while (pred_begin(Exit1) != pred_end(Exit1))
		{
			(*(pred_begin(Exit1)))->getTerminator()->replaceSuccessorWith(Exit1, PreHeader2);
		}
		Exit1->eraseFromParent();
	}

	/* Final check before return */
	if (L1->getExitBlock() == L2->getLoopPreheader() && L2->getLoopPreheader()->size() == 1)
	{
		return true;
	}

	//errs() << "can not make adj\n";
	return false;
} /* tryMakeLoopsAdjacent */

bool
processSet(std::list<Loop *> &set, ScalarEvolution &SE, DependenceInfo &DI)
{
	for (auto it1 = set.begin(), it1e = set.end(); it1 != it1e; ++it1)
	{
		Loop *L1 = *it1;
		for (auto it2 = std::next(it1), it2e = set.end(); it2 != it2e; ++it2)
		{
			Loop *L2 = *it2;
			const SCEV *TripCount1 = SE.getSymbolicMaxBackedgeTakenCount(L1);
			const SCEV *TripCount2 = SE.getSymbolicMaxBackedgeTakenCount(L2);
			if (TripCount1->getSCEVType() == SCEVTypes::scCouldNotCompute ||
				TripCount2->getSCEVType() == SCEVTypes::scCouldNotCompute)
			{
				continue;
			}
			if (TripCount1 != TripCount2)
			{
				continue;
			}
			if (loopsHaveInvalidDependencies(L1, L2, DI))
			{
				continue;
			}
			if (tryMakeLoopsAdjacent(L1, L2, DI) == false)
			{
				continue;
			}

			/* Finally, fuse loops */
			fuse(L1, L2);
			return true;
		}
	}
	return false;
} /* processSet */

bool
processLoops(const SmallVector<Loop *> &Loops, const DominatorTree &DT, const PostDominatorTree &PDT, ScalarEvolution &SE, DependenceInfo &DI)
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
		fused |= processSet(set, SE, DI);
	}
	return fused;
} /* processLoops */

/* Deprecated */
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
	bool changed = false;

	unsigned LoopCount;
	if (DebugMode)
	{
		LoopCount = FAM.getResult<LoopAnalysis>(F).getLoopsInPreorder().size();
		errs() << "Func: " << F.getName() << "\n";
		errs() << "\tloop count before: " << LoopCount << "\n";
	}
	SmallVector<Loop *> LoopsToProcess;
	unsigned i = 1;
	while (true)
	{
		/* Get analyses */
		LoopInfo          &LI  = FAM.getResult<LoopAnalysis>(F);
		DominatorTree     &DT  = FAM.getResult<DominatorTreeAnalysis>(F);
		PostDominatorTree &PDT = FAM.getResult<PostDominatorTreeAnalysis>(F);
		ScalarEvolution   &SE  = FAM.getResult<ScalarEvolutionAnalysis>(F);
		DependenceInfo    &DI  = FAM.getResult<DependenceAnalysis>(F);

		LoopsToProcess = collectLoopsAtDepth(LI, i);
		if (LoopsToProcess.empty())
		{
			break;
		}

		bool FusedAny = processLoops(LoopsToProcess, DT, PDT, SE, DI);
		if (FusedAny)
		{
			changed = true;

			/* Invalidate analyses since CFG changed */
			FAM.invalidate(F, PreservedAnalyses::none());
		}
		else
		{
			i++;
		}
	}
	if (DebugMode)
	{
		if (changed)
			LoopCount = FAM.getResult<LoopAnalysis>(F).getLoopsInPreorder().size();
		errs()	<< "\tloop count after : " << LoopCount << "\n";
	}
	return changed;
} /* FuseLoops */

struct FusionPass : PassInfoMixin<FusionPass> 
{
	PreservedAnalyses 
	run(Function &F, FunctionAnalysisManager &FAM) 
	{
		bool changed = FuseLoops(F, FAM);
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
