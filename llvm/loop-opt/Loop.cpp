#include "llvm/Analysis/ValueTracking.h"
#include "llvm/Pass.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;

namespace {
struct CustomLoopPass : public PassInfoMixin<CustomLoopPass> {
  static bool isRequired() { return true; }

  bool isLoopInvariant(Instruction &instr, Loop &L,
                       SmallPtrSet<Instruction *, 16> &inv_set) {
    // instructions with side effects are NOT safe to move
    if (!isSafeToSpeculativelyExecute(&instr))
      return false;

    // check if operands are either defined outside of the loop or are
    // loop-invariant themselves
    for (Value *op : instr.operands()) {
      if (Instruction *op_instr = dyn_cast<Instruction>(op)) {
        if (L.contains(op_instr) && !inv_set.contains(op_instr))
          return false;
      }
    }

    return true;
  }

  bool isSafeToHoist(Instruction *instr, Loop &L) {
    // chech dominance of uses
    for (User *u : instr->users()) {
      if (!L.isLoopInvariant(u)) {
        errs() << "did not hoist " << *u << "\n";
        return false;
      }
    }
    return true;
  }

  PreservedAnalyses run(Loop &L, LoopAnalysisManager &AM,
                        LoopStandardAnalysisResults &AR, LPMUpdater &Updater) {
    errs() << "Performing LICM Pass...\n";

    auto *preheader = L.getLoopPreheader();
    if (!preheader) {
      errs() << "loop does not have preheader, skipping LICM\n";
      return PreservedAnalyses::all();
    }

    SmallPtrSet<Instruction *, 16> loop_invariant_instrs;
    for (auto *BB : L.blocks()) {
      for (auto &instr : *BB) {
        if (isLoopInvariant(instr, L, loop_invariant_instrs)) {
          errs() << instr << " marked as invariant.\n";
          loop_invariant_instrs.insert(&instr);
        }
      }
    }

    for (Instruction *instr : loop_invariant_instrs) {
      if (isSafeToHoist(instr, L)) {
        errs() << *instr << " hoisted to preheader.\n";
        instr->moveBefore(preheader->getTerminator());
      }
    }

    return PreservedAnalyses::none();
  }
};

extern "C" LLVM_ATTRIBUTE_WEAK ::llvm::PassPluginLibraryInfo
llvmGetPassPluginInfo() {
  return {.APIVersion = LLVM_PLUGIN_API_VERSION,
          .PluginName = "Skeleton pass",
          .PluginVersion = "v0.1",
          .RegisterPassBuilderCallbacks = [](PassBuilder &PB) {
            PB.registerPipelineParsingCallback(
                [](StringRef Name, LoopPassManager &LPM,
                   ArrayRef<PassBuilder::PipelineElement>) {
                  if (Name == "custom-loop-pass") {
                    LPM.addPass(CustomLoopPass());
                    return true;
                  }
                  return false;
                });
          }};
}
} // namespace
