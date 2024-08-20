#include "llvm/IR/Dominators.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Support/raw_ostream.h"
#include <set>
#include <vector>

using namespace llvm;

namespace {

bool
blockContainsVolatileInst(const BasicBlock &BB)
{
	for (const Instruction &I : BB)
	{
		if (I.isVolatile())
		{
			return true;
		}
	}
	return false;
}

bool
loopContainsVolatileInst(const Loop &L)
{
	for (BasicBlock *BB : L.blocks())
	{
		//outs() << BB->getNumber() << "(" << BB->size() << ")_";
		if (blockContainsVolatileInst(*BB))
		{
			return true;
		}
	}
	//outs() << "size: " << L.getNumBlocks() << "\n";
	return false;
}

bool
loopDominates(Loop *L1, Loop *L2, DominatorTree &DT)
{
	//SmallVector<BasicBlock *> L1ExitBBs, L2ExitBBs;
	//L1->getExitingBlocks(L1ExitBBs);
	//L2->getExitingBlocks(L2ExitBBs);
	//outs() << L1ExitBBs.size() << " " << L2ExitBBs.size() << "\n";
	const auto H1 = L1->getLoopPreheader();
	const auto H2 = L2->getLoopPreheader();
	return DT.properlyDominates(H1, H2);
	/*for (BasicBlock *BB1 : L1ExitBBs)
	{
		for (BasicBlock *BB2 : L2ExitBBs)
		{
			if (DT.properlyDominates(BB1, BB2) == false)
			{
				outs() << "NO\n";
				return false;
			}
		}
	}
	return true;*/
}

bool
loopPostDominates(Loop *L1, Loop *L2, PostDominatorTree &PDT)
{
	const auto H1 = L1->getLoopPreheader();
	const auto H2 = L2->getLoopPreheader();
	return PDT.properlyDominates(H1, H2);

}

bool
FuseLoops(Function &F, FunctionAnalysisManager &AM)
{
	
	outs() << "Func: " << F.getName() << "\n";
	LoopInfo &li = AM.getResult<LoopAnalysis>(F);
	//li.print(outs());
	const std::vector<Loop *> &TopLoops = li.getTopLevelLoops();

	/* Collect candidates */
	std::set<Loop *> Candidates;
	for (Loop *L : TopLoops)
	{
		//outs() << L->isLoopSimplifyForm() << "\n";
		if (L->isLoopSimplifyForm() && loopContainsVolatileInst(*L) == false)
		{
			Candidates.insert(L);
		}
	}

	DominatorTree		DT(F);
	PostDominatorTree	PDT(F);
	
	/* Build Control Flow Equivalent sets */
	std::vector<std::vector<Loop *>> CFEs;
	for (auto it = Candidates.begin(), ite = Candidates.end(); it != ite; ++it)
	{
		//std::vector A;
		//A.push_back(*it);
		CFEs.push_back(std::vector<Loop *> {*it});
	}
	for (auto it1 = CFEs.begin(), it1e = CFEs.end(); it1 != it1e; ++it1)
	{
		Loop *L1 = (*it1)[0];
		
		for (auto it2 = Candidates.begin(), it2e = Candidates.end(); it2 != it2e;)
		{
			Loop *L2 = *it2;
			if (loopDominates(L1, L2, DT) && loopPostDominates(L2, L1, PDT))
			{
				outs() << "	yes\n";
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
			[](const std::vector<Loop *> v)
			{
				return v.size() == 1;
			}
		),
		CFEs.end()
	);
	outs() << CFEs.size() << "__\n";

	for (auto &set : CFEs)
	{
		
	}

	bool fused = false;

	return fused;
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
