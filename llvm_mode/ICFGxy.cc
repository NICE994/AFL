//ICFGxy.cc
//SAYF(cCYA "cgFilename " cBRI VERSION cRST " (%s mode)\n",cgFilename.c_str());
#include "llvm/Analysis/CallPrinter.h"
#include "llvm/Analysis/BlockFrequencyInfo.h"
#include "llvm/Analysis/BranchProbabilityInfo.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Analysis/DOTGraphTraitsPass.h"
#include "llvm/Analysis/HeatUtils.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/InitializePasses.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/SmallSet.h"

using namespace llvm;

namespace llvm{

class ICFGDOTInfo{
private:
  Module *M;
  CallGraph *CG;
  //没有CallMap这个类
  CallMap<Function &callerFunction, Function &calledFunction> CallSites;

public:
  std::function<BlockFrequencyInfo *(Function &)> LookupBFI;

  ICFGDOTInfo(Module *M, CallGraph *CG)
        :M(M),CG(CG){
          
  //构建调用关系
  for(Function &F:M->getFunctionList()){
    SmallSet<Function *, 16> Callers;
    for (User *U : F.users()) //User表示Instruction？
    {
      if (isa<CallInst>(U))
      {
        Callers.insert(cast<Instruction>(U)->getFunction());
      }
    }
    //打印查看Caller的内容
    //SAYF(cCYA "Callers<> " cBRI VERSION cRST " (%s mode)\n",cgFilename.c_str());
  }
  Module *getModule() const { return M; }

  CallGraph *getCallGraph() const { return CG; }

  
  }

private:
  ;
};

template<>
struct GraphTraits<ICFGDOTInfo *>
  : public GraphTraits<const CallGraphNode *>{
  static NodeRef getEntryNode(ICFGDOTInfo *CGInfo) {
    // Start at the external node!
    return CGInfo->getCallGraph()->getExternalCallingNode();  
  }

  typedef std::pair<const Function *const, std::unique_ptr<CallGraphNode>>
      PairTy;
  static const CallGraphNode *CGGetValuePtr(const PairTy &P) {
    return P.second.get();
  }

  // nodes_iterator/begin/end - Allow iteration over all nodes in the graph
  typedef mapped_iterator<CallGraph::const_iterator, decltype(&CGGetValuePtr)>
      nodes_iterator;

  static nodes_iterator nodes_begin(ICFGDOTInfo *CGInfo) {
    return nodes_iterator(CGInfo->getCallGraph()->begin(), &CGGetValuePtr);
  }
  static nodes_iterator nodes_end(ICFGDOTInfo *CGInfo) {
    return nodes_iterator(CGInfo->getCallGraph()->end(), &CGGetValuePtr);
  }
}