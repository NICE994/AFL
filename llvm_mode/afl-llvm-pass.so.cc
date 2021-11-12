/*
  Copyright 2015 Google LLC All rights reserved.

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at:

    http://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.
*/

/*
   american fuzzy lop - LLVM-mode instrumentation pass
   ---------------------------------------------------

   Written by Laszlo Szekeres <lszekeres@google.com> and
              Michal Zalewski <lcamtuf@google.com>

   LLVM integration design comes from Laszlo Szekeres. C bits copied-and-pasted
   from afl-as.c are Michal's fault.

   This library is plugged into LLVM when invoking clang through afl-clang-fast.
   It tells the compiler to add code roughly equivalent to the bits discussed
   in ../afl-as.h.
*/

#define AFL_LLVM_PASS

#include "../config.h"
#include "../debug.h"

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

#include <iostream>
#include <fstream>
#include <string>
#include <sstream>
#include <list>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>

#include "llvm/ADT/Statistic.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/Debug.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"

#include "llvm/Support/CommandLine.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/raw_ostream.h"
//#include "llvm/Analysis/CFGPrinter.h"

#include "llvm/Analysis/CallPrinter.h"
#include "llvm/Analysis/BlockFrequencyInfo.h"
//#include "llvm/Analysis/BranchProbabilityInfo.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Analysis/DOTGraphTraitsPass.h"
#include "llvm/Analysis/HeatUtils.h"
//#include "llvm/Support/CommandLine.h"
#include "llvm/InitializePasses.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/SmallSet.h"

#if defined(LLVM34)
#include "llvm/DebugInfo.h"
#else
#include "llvm/IR/DebugInfo.h"
#endif

#if defined(LLVM34) || defined(LLVM35) || defined(LLVM36)
#define LLVM_OLD_DEBUG_API
#endif

using namespace llvm;

/*
cl::opt<std::string> OutDirectory( //没有读到对应的参数
    "outdir",
    cl::desc("Output directory where Ftargets.txt, Fnames.txt, and BBnames.txt are generated."),
    cl::value_desc("outdir"));
    

static cl::opt<bool> ShowHeatColors("callgraph-heat-colors", cl::init(false),
                                    cl::Hidden,
                                    cl::desc("Show heat colors in call-graph"));

static cl::opt<bool>
    ShowEdgeWeight("callgraph-show-weights", cl::init(false), cl::Hidden,
                       cl::desc("Show edges labeled with weights"));

static cl::opt<bool>
    CallMultiGraph("callgraph-multigraph", cl::init(false), cl::Hidden,
            cl::desc("Show call-multigraph (do not remove parallel edges)"));

static cl::opt<std::string> CallGraphDotFilenamePrefix(
    "callgraph-dot-filename-prefix", cl::Hidden,
    cl::desc("The prefix used for the CallGraph dot file names."));
*/

std::string OutDirectory("/home/xy/Desktop/test");
int ShowHeatColors = 0;
int ShowEdgeWeight = 0;
bool CallMultiGraph = false;
std::string CallGraphDotFilenamePrefix("cgg");

namespace llvm {

  class CallGraphDOTInfo {
private:
  Module *M;
  CallGraph *CG;
  DenseMap<const Function *, uint64_t> Freq;
  uint64_t MaxFreq;

public:
  std::function<BlockFrequencyInfo *(Function &)> LookupBFI;

  CallGraphDOTInfo(Module *M, CallGraph *CG,
                   function_ref<BlockFrequencyInfo *(Function &)> LookupBFI)
      : M(M), CG(CG), LookupBFI(LookupBFI) {
    MaxFreq = 0;

    for (Function &F : M->getFunctionList()) {
      uint64_t localSumFreq = 0;
      SmallSet<Function *, 16> Callers; //构建一个集合，caller的集合
      for (User *U : F.users())
        if (isa<CallInst>(U))
          Callers.insert(cast<Instruction>(U)->getFunction());
      for (Function *Caller : Callers)
        localSumFreq += getNumOfCalls(*Caller, F);
      if (localSumFreq >= MaxFreq)
        MaxFreq = localSumFreq;
      Freq[&F] = localSumFreq;
    }
    //if (!CallMultiGraph)
      //removeParallelEdges();
  }

  Module *getModule() const { return M; }

  CallGraph *getCallGraph() const { return CG; }

  uint64_t getFreq(const Function *F) { return Freq[F]; }

  uint64_t getMaxFreq() { return MaxFreq; }

private:
  void removeParallelEdges() {
    for (auto &I : (*CG)) {
      CallGraphNode *Node = I.second.get();

      bool FoundParallelEdge = true;
      while (FoundParallelEdge) {
        SmallSet<Function *, 16> Visited;
        FoundParallelEdge = false;
        for (auto CI = Node->begin(), CE = Node->end(); CI != CE; CI++) {
          if (!(Visited.insert(CI->second->getFunction())).second) {
            FoundParallelEdge = true;
            Node->removeCallEdge(CI);
            break;
          }
        }
      }
    }
  }
  };

template <>
struct GraphTraits<CallGraphDOTInfo *>
    : public GraphTraits<const CallGraphNode *> {
  static NodeRef getEntryNode(CallGraphDOTInfo *CGInfo) {
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

  static nodes_iterator nodes_begin(CallGraphDOTInfo *CGInfo) {
    return nodes_iterator(CGInfo->getCallGraph()->begin(), &CGGetValuePtr);
  }
  static nodes_iterator nodes_end(CallGraphDOTInfo *CGInfo) {
    return nodes_iterator(CGInfo->getCallGraph()->end(), &CGGetValuePtr);
  }
};

template <>
struct DOTGraphTraits<CallGraphDOTInfo *> : public DefaultDOTGraphTraits {

  DOTGraphTraits(bool isSimple = false) : DefaultDOTGraphTraits(isSimple) {}

  static std::string getGraphName(CallGraphDOTInfo *CGInfo) {
    return "Call graph: " +
           std::string(CGInfo->getModule()->getModuleIdentifier());
  }

  /*xy
  static bool isNodeHidden(const CallGraphNode *Node,
                           const CallGraphDOTInfo *CGInfo) {
    if (CallMultiGraph || Node->getFunction())
      return false;
    return true;
  }
  */

  std::string getNodeLabel(const CallGraphNode *Node,
                           CallGraphDOTInfo *CGInfo) {
    if (Node == CGInfo->getCallGraph()->getExternalCallingNode())
      return "external caller";
    if (Node == CGInfo->getCallGraph()->getCallsExternalNode())
      return "external callee";

    if (Function *Func = Node->getFunction())
      return std::string(Func->getName());
    return "external node";
  }
  static const CallGraphNode *CGGetValuePtr(CallGraphNode::CallRecord P) {
    return P.second;
  }

  // nodes_iterator/begin/end - Allow iteration over all nodes in the graph
  typedef mapped_iterator<CallGraphNode::const_iterator,
                          decltype(&CGGetValuePtr)>
      nodes_iterator;

  std::string getEdgeAttributes(const CallGraphNode *Node, nodes_iterator I,
                                CallGraphDOTInfo *CGInfo) {
    if (!ShowEdgeWeight)
      return "";

    Function *Caller = Node->getFunction();
    if (Caller == nullptr || Caller->isDeclaration())
      return "";

    Function *Callee = (*I)->getFunction();
    if (Callee == nullptr)
      return "";

    uint64_t Counter = getNumOfCalls(*Caller, *Callee);
    double Width =
        1 + 2 * (double(Counter) / CGInfo->getMaxFreq());
    std::string Attrs = "label=\"" + std::to_string(Counter) +
                        "\" penwidth=" + std::to_string(Width);
    return Attrs;
  }

  std::string getNodeAttributes(const CallGraphNode *Node,
                                CallGraphDOTInfo *CGInfo) {
    Function *F = Node->getFunction();
    if (F == nullptr)
      return "";
    std::string attrs;
    if (ShowHeatColors) {
      uint64_t freq = CGInfo->getFreq(F);
      std::string color = getHeatColor(freq, CGInfo->getMaxFreq());
      std::string edgeColor = (freq <= (CGInfo->getMaxFreq() / 2))
                                  ? getHeatColor(0)
                                  : getHeatColor(1);
      attrs = "color=\"" + edgeColor + "ff\", style=filled, fillcolor=\"" +
              color + "80\"";
    }
    return attrs;
  }
};

template<>
struct DOTGraphTraits<Function*> : public DefaultDOTGraphTraits { //重写DOTGraphTraits
  DOTGraphTraits(bool isSimple=true) : DefaultDOTGraphTraits(isSimple) {}

  static std::string getGraphName(Function *F) {
    return "CFG for '" + F->getName().str() + "' function";
  }

  std::string getNodeLabel(BasicBlock *Node, Function *Graph) {
    if (!Node->getName().empty()) {
      return Node->getName().str();
    }

    std::string Str;
    raw_string_ostream OS(Str);

    Node->printAsOperand(OS, false);
    return OS.str();
  }
};
}//namespace llvm

namespace {

  class AFLCoverage : public ModulePass {

    public:

      static char ID;
      AFLCoverage() : ModulePass(ID) { }

      bool runOnModule(Module &M) override;

      // StringRef getPassName() const override {
      //  return "American Fuzzy Lop Instrumentation";
      // }

  };

}


char AFLCoverage::ID = 0;

static void getDebugLoc(const Instruction *I, std::string &Filename,
                        unsigned &Line) { //获取指令的文件位置
#ifdef LLVM_OLD_DEBUG_API
  DebugLoc Loc = I->getDebugLoc();
  if (!Loc.isUnknown()) {
    DILocation cDILoc(Loc.getAsMDNode(M.getContext()));
    DILocation oDILoc = cDILoc.getOrigLocation();

    Line = oDILoc.getLineNumber();
    Filename = oDILoc.getFilename().str();

    if (filename.empty()) {
      Line = cDILoc.getLineNumber();
      Filename = cDILoc.getFilename().str();
    }
  }
#else
  if (DILocation *Loc = I->getDebugLoc()) {
    Line = Loc->getLine();
    Filename = Loc->getFilename().str();

    if (Filename.empty()) {
      DILocation *oDILoc = Loc->getInlinedAt();
      if (oDILoc) {
        Line = oDILoc->getLine();
        Filename = oDILoc->getFilename().str();
      }
    }
  }
#endif /* LLVM_OLD_DEBUG_API */
}

static bool isBlacklisted(const Function *F) { //黑名单函数，在遍历到这些函数时特殊处理
  static const SmallVector<std::string, 8> Blacklist = {
    "asan.",
    "llvm.",
    "sancov.",
    "__ubsan_handle_",
    "free",
    "malloc",
    "calloc",
    "realloc"
  };

  for (auto const &BlacklistFunc : Blacklist) {
    if (F->getName().startswith(BlacklistFunc)) {
      return true;
    }
  }

  return false;
}


bool AFLCoverage::runOnModule(Module &M) {

  LLVMContext &C = M.getContext();

  IntegerType *Int8Ty  = IntegerType::getInt8Ty(C);
  IntegerType *Int32Ty = IntegerType::getInt32Ty(C);

  //SAYF(cCYA "aflgo-llvm-pass (yeah!) " cBRI VERSION cRST " (%s mode)\n",(true ? "preprocessing" : "distance instrumentation")); //这是一个可以直接在终端打印的函数

  /* Show a banner */

  char be_quiet = 0;

  if (isatty(2) && !getenv("AFL_QUIET")) {

    SAYF(cCYA "afl-llvm-pass " cBRI VERSION cRST " by <lszekeres@google.com>\n");

  } else be_quiet = 1;

  /* Decide instrumentation ratio */

  char* inst_ratio_str = getenv("AFL_INST_RATIO");
  unsigned int inst_ratio = 100;

  if (inst_ratio_str) {

    if (sscanf(inst_ratio_str, "%u", &inst_ratio) != 1 || !inst_ratio ||
        inst_ratio > 100)
      FATAL("Bad value of AFL_INST_RATIO (must be between 1 and 100)");

  }

  //构建ICFG
  //int inst_block = 0; //插桩代码

  //if(is_aflgo_preprocessing){
  if(true){
    std::ofstream bbnames(OutDirectory + "/BBnames.txt", std::ofstream::out | std::ofstream::app);
    std::ofstream bbcalls(OutDirectory + "/BBcalls.txt", std::ofstream::out | std::ofstream::app);
    std::ofstream fnames(OutDirectory + "/Fnames.txt", std::ofstream::out | std::ofstream::app);
    std::ofstream ftargets(OutDirectory + "/Ftargets.txt", std::ofstream::out | std::ofstream::app);

    /* Create dot-files directory */
    std::string dotfiles(OutDirectory + "/dot-files");
    //std::string dotfiles("/home/xy/Desktop/dot-files");

    SAYF(cCYA "OutDirectory " cBRI VERSION cRST " (%s mode)\n",OutDirectory.c_str());
    
    if (sys::fs::create_directory(dotfiles)) {
      FATAL("Could not create directory %s.", dotfiles.c_str());
    }

    for (auto &F : M) {

      bool has_BBs = false;
      std::string funcName = F.getName().str();

      /* Black list of function names */
      if (isBlacklisted(&F)) {
        continue;
      }

      //bool is_target = false;
      for (auto &BB : F) {

        std::string bb_name("");
        std::string filename;
        unsigned line;

        for (auto &I : BB) { //对基本块中的每条指令进行处理；

          getDebugLoc(&I, filename, line);

          /* Don't worry about external libs */
          static const std::string Xlibs("/usr/");
          if (filename.empty() || line == 0 || !filename.compare(0, Xlibs.size(), Xlibs))
            continue;

          if (bb_name.empty()) {

            std::size_t found = filename.find_last_of("/\\");
            if (found != std::string::npos)
              filename = filename.substr(found + 1);

            bb_name = filename + ":" + std::to_string(line);//为每个基本块使用文件名:行数的方法命名了
          }

          if (auto *c = dyn_cast<CallInst>(&I)) {//动态转换，判断I是否是callinst

              std::size_t found = filename.find_last_of("/\\");
              if (found != std::string::npos)
                filename = filename.substr(found + 1);

              if (auto *CalledF = c->getCalledFunction()) {//得到调用函数的文件位置，被调用的函数
                if (!isBlacklisted(CalledF)){
                  bbcalls << bb_name << "," << CalledF->getName().str() << "\n";
                  
                }
              }
          }
        }

        if (!bb_name.empty()) {

          BB.setName(bb_name + ":");
          //SAYF(cCYA "bb_name " cBRI VERSION cRST " (%s mode)\n",BB.getName().str().c_str());
          if (!BB.hasName()) { //这一段代码应该是不会被执行的？？
            std::string newname = bb_name + ":";
            Twine t(newname);
            SmallString<256> NameData;
            StringRef NameRef = t.toStringRef(NameData);
            MallocAllocator Allocator;
            BB.setValueName(ValueName::Create(NameRef, Allocator));
          }

          bbnames << BB.getName().str() << "\n";
          has_BBs = true;  //对应的Function含有BB

        }

      }

      if (has_BBs) {
        /* Print CFG */
        std::string cfgFileName = dotfiles + "/cfg." + funcName + ".dot";
        std::error_code EC;
        raw_fd_ostream cfgFile(cfgFileName, EC, sys::fs::F_None);
        if (!EC) {
          WriteGraph(cfgFile, &F, true); //不再对function级画Intraprocedure控制流图
        }
      }
    }

    /* 尝试打印module里的Function图 
    std::string cfgFileName_function = dotfiles + "/cfg-function." + M.getName().str() + ".dot";
    std::error_code EC2;
    raw_fd_ostream cfgFile_function(cfgFileName_function, EC2, sys::fs::F_None);
    if (!EC2)
    {
      //WriteGraph(cfgFile_function, &M, true); //不再对function级画Intraprocedure控制流图
      //不能直接对Module进行打印，需要进行转换
    }*/

    auto LookupBFI = [this](Function &F)
    {
      return &this->getAnalysis<BlockFrequencyInfoWrapperPass>(F).getBFI();
    };

    std::string cgFilename;
    cgFilename = (OutDirectory + "/dot-files/cg.callgraph.dot");
    SAYF(cCYA "cgFilename " cBRI VERSION cRST " (%s mode)\n",cgFilename.c_str());

    std::error_code cgEC;
    raw_fd_ostream cgFile(cgFilename, cgEC, sys::fs::OF_Text);

    CallGraph CG(M);
    //调用CallGraph的print（）
    std::string CGprintN = dotfiles + "/cgprint.txt";
    std::error_code cgpEC;
    raw_fd_ostream cgpFile(CGprintN, cgpEC, sys::fs::F_None);

    CG.print(cgpFile);

    CallGraphDOTInfo CFGInfo(&M, &CG, LookupBFI);

    if (!cgEC)
      WriteGraph(cgFile, &CFGInfo);
    else
      errs() << "  error opening file for writing!";
    errs() << "\n";
  }

  /* Get globals for the SHM region and the previous location. Note that
     __afl_prev_loc is thread-local. */

  GlobalVariable *AFLMapPtr =
      new GlobalVariable(M, PointerType::get(Int8Ty, 0), false,
                         GlobalValue::ExternalLinkage, 0, "__afl_area_ptr");

  GlobalVariable *AFLPrevLoc = new GlobalVariable(
      M, Int32Ty, false, GlobalValue::ExternalLinkage, 0, "__afl_prev_loc",
      0, GlobalVariable::GeneralDynamicTLSModel, 0, false);

  /* Instrument all the things! */

  int inst_blocks = 0;

  for (auto &F : M)
    for (auto &BB : F) {

      BasicBlock::iterator IP = BB.getFirstInsertionPt();
      IRBuilder<> IRB(&(*IP));

      if (AFL_R(100) >= inst_ratio) continue;

      /* Make up cur_loc */

      unsigned int cur_loc = AFL_R(MAP_SIZE);

      ConstantInt *CurLoc = ConstantInt::get(Int32Ty, cur_loc);

      /* Load prev_loc */

      LoadInst *PrevLoc = IRB.CreateLoad(AFLPrevLoc);
      PrevLoc->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
      Value *PrevLocCasted = IRB.CreateZExt(PrevLoc, IRB.getInt32Ty());

      /* Load SHM pointer */

      LoadInst *MapPtr = IRB.CreateLoad(AFLMapPtr);
      MapPtr->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
      Value *MapPtrIdx =
          IRB.CreateGEP(MapPtr, IRB.CreateXor(PrevLocCasted, CurLoc));

      /* Update bitmap */

      LoadInst *Counter = IRB.CreateLoad(MapPtrIdx);
      Counter->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
      Value *Incr = IRB.CreateAdd(Counter, ConstantInt::get(Int8Ty, 1));
      IRB.CreateStore(Incr, MapPtrIdx)
          ->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

      /* Set prev_loc to cur_loc >> 1 */

      StoreInst *Store =
          IRB.CreateStore(ConstantInt::get(Int32Ty, cur_loc >> 1), AFLPrevLoc);
      Store->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

      inst_blocks++;

    }

  /* Say something nice. */

  if (!be_quiet) {

    if (!inst_blocks) WARNF("No instrumentation targets found.");
    else OKF("Instrumented %u locations (%s mode, ratio %u%%).",
             inst_blocks, getenv("AFL_HARDEN") ? "hardened" :
             ((getenv("AFL_USE_ASAN") || getenv("AFL_USE_MSAN")) ?
              "ASAN/MSAN" : "non-hardened"), inst_ratio);

  }

  return true;

}


static void registerAFLPass(const PassManagerBuilder &,
                            legacy::PassManagerBase &PM) {

  PM.add(new AFLCoverage());

}


static RegisterStandardPasses RegisterAFLPass(
    PassManagerBuilder::EP_ModuleOptimizerEarly, registerAFLPass);

static RegisterStandardPasses RegisterAFLPass0(
    PassManagerBuilder::EP_EnabledOnOptLevel0, registerAFLPass);
