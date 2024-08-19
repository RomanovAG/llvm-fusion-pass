#include <functional>
#include "llvm/IR/Dominators.h"
//#include "llvm/IR/InstIterator.h"
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
FuseLoops(Function &F, FunctionAnalysisManager &AM)
{
	
	outs() << "Func: " << F.getName() << "\n";
	LoopInfo &li = AM.getResult<LoopAnalysis>(F);
	//li.print(outs());
	const std::vector<Loop *> &TopLoops = li.getTopLevelLoops();

	std::vector<Loop *> Candidates;
	for (Loop *L : TopLoops)
	{
		//outs() << L->isLoopSimplifyForm() << "\n";
		if (L->isLoopSimplifyForm() && loopContainsVolatileInst(*L) == false)
		{
			Candidates.push_back(L);
		}
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
