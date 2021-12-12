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
#include "../hash.h"
#include "../hashset.h"

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <string>
#include <fstream>
#include <sstream>
#include <sys/stat.h>

#include "llvm/ADT/Statistic.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/Debug.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"

using namespace llvm;
using namespace std;


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

// HorseFuzz
static hashset_t funcSet = hashset_create();
ofstream outfile, outfile1, outfile2;

static const unsigned int prime_1 = 73;
static const unsigned int prime_2 = 5009;

/* Hashset implementation for C */
hashset_t hashset_create()
{
  hashset_t set = (hashset_t) calloc(1, sizeof(struct hashset_st));

  if (set == NULL) {
    return NULL;
  }
  set->nbits = 3;
  set->capacity = (size_t)(1 << set->nbits);
  set->mask = set->capacity - 1;
  set->items = (unsigned long*) calloc(set->capacity, sizeof(size_t));
  if (set->items == NULL) {
    hashset_destroy(set);
    return NULL;
  }
  set->nitems = 0;
  set->n_deleted_items = 0;
  return set;
}

size_t hashset_num_items(hashset_t set)
{
  return set->nitems;
}

void hashset_destroy(hashset_t set)
{
  if (set) {
    free(set->items);
  }
  free(set);
}

static int hashset_add_member(hashset_t set, void *item)
{
  size_t value = (size_t)item;
  size_t ii;

  if (value == 0 || value == 1) {
    return -1;
  }

  ii = set->mask & (prime_1 * value);

  while (set->items[ii] != 0 && set->items[ii] != 1) {
    if (set->items[ii] == value) {
      return 0;
    } else {
      /* search free slot */
      ii = set->mask & (ii + prime_2);
    }
  }
  set->nitems++;
  if (set->items[ii] == 1) {
    set->n_deleted_items--;
  }
  set->items[ii] = value;
  return 1;
}

static void maybe_rehash(hashset_t set)
{
  size_t *old_items;
  size_t old_capacity, ii;


  if (set->nitems + set->n_deleted_items >= (double)set->capacity * 0.85) {
    old_items = set->items;
    old_capacity = set->capacity;
    set->nbits++;
    set->capacity = (size_t)(1 << set->nbits);
    set->mask = set->capacity - 1;
    set->items = (unsigned long*) calloc(set->capacity, sizeof(size_t));
    set->nitems = 0;
    set->n_deleted_items = 0;
    assert(set->items);
    for (ii = 0; ii < old_capacity; ii++) {
      hashset_add_member(set, (void *)old_items[ii]);
    }
    free(old_items);
  }
}

int hashset_add(hashset_t set, void *item)
{
  int rv = hashset_add_member(set, item);
  maybe_rehash(set);
  return rv;
}

int hashset_remove(hashset_t set, void *item)
{
  size_t value = (size_t)item;
  size_t ii = set->mask & (prime_1 * value);

  while (set->items[ii] != 0) {
    if (set->items[ii] == value) {
      set->items[ii] = 1;
      set->nitems--;
      set->n_deleted_items++;
      return 1;
    } else {
      ii = set->mask & (ii + prime_2);
    }
  }
  return 0;
}

int hashset_is_member(hashset_t set, void *item)
{
  size_t value = (size_t)item;
  size_t ii = set->mask & (prime_1 * value);

  while (set->items[ii] != 0) {
    if (set->items[ii] == value) {
        return 1;
    } else {
        ii = set->mask & (ii + prime_2);
    }
  }
  return 0;
}

/*End of hashset implementation for C */

bool sortByVal(const pair<string, int> &a, const pair<string, int> &b) {
  return (a.second < b.second);
}

bool AFLCoverage::runOnModule(Module &M) {

  // HorseFuzz: parse file name
  std::string module_str(M.getName().data());
  std::size_t found = module_str.find_last_of("/\\");
  std::string file_name = module_str.substr(found+1);
  // SAYF("Module: %s, file name: %s\n", module_str.c_str(), file_name.c_str());

  std::string binary(getenv("HF_BINARY"));
  std::string tmp_dir = "/tmp/" + binary;
  std::string fn_funcs = tmp_dir + "/func_ids.log";
  std::string fn_bbs = tmp_dir + "/func_bbs.log";
  //std::string fn_ind_calls = tmp_dir + "/indirected_calls.log";

  //if (mkdir(tmp_dir.c_str(), 0700)) PFATAL("Unable to create '%s'", tmp_dir.c_str());

  outfile.open(fn_funcs.c_str(), std::ofstream::out | std::ofstream::app);
  outfile1.open(fn_bbs.c_str(), std::ofstream::out | std::ofstream::app);
  //outfile2.open(fn_ind_calls.c_str(), std::ofstream::out | std::ofstream::app);

  LLVMContext &C = M.getContext();

  IntegerType *Int8Ty  = IntegerType::getInt8Ty(C);
  IntegerType *Int32Ty = IntegerType::getInt32Ty(C);

  /* Show a banner */

  char be_quiet = 0;

  if (isatty(2) && !getenv("AFL_QUIET")) {

    SAYF(cCYA "horsefuzz-llvm-pass HorseFuzz " cBRI VERSION cRST " by <lszekeres@google.com>\n");

  } else be_quiet = 1;

  /* Decide instrumentation ratio */

  char* inst_ratio_str = getenv("AFL_INST_RATIO");
  unsigned int inst_ratio = 100;

  if (inst_ratio_str) {

    if (sscanf(inst_ratio_str, "%u", &inst_ratio) != 1 || !inst_ratio ||
        inst_ratio > 100)
      FATAL("Bad value of AFL_INST_RATIO (must be between 1 and 100)");

  }

  /* Get globals for the SHM region and the previous location. Note that
     __afl_prev_loc is thread-local. */

  GlobalVariable *AFLMapPtr =
      new GlobalVariable(M, PointerType::get(Int8Ty, 0), false,
                         GlobalValue::ExternalLinkage, 0, "__afl_area_ptr");

  // HorseFuzz
  GlobalVariable *AFLFuncIDPtr =
      new GlobalVariable(M, PointerType::get(Int32Ty, 0), false,
                        GlobalValue::ExternalLinkage, 0, "__afl_funcids_ptr");

  GlobalVariable *AFLPrevLoc = new GlobalVariable(
      M, Int32Ty, false, GlobalValue::ExternalLinkage, 0, "__afl_prev_loc",
      0, GlobalVariable::GeneralDynamicTLSModel, 0, false);

  /* Instrument all the things! */

  int inst_blocks = 0;
  std::map<std::string,int> fb;
  int nb_indirected_calls = 0;

  for (auto &F : M) {

    std::string funcName = F.getName();
    std::string fileFuncName = file_name + ":" + funcName;

    /* Black list of function names */
    // std::vector<std::string> blacklist = {
    //   "asan.",
    //   "llvm.",
    //   "sancov.",
    //   "free"
    //   "malloc",
    //   "calloc",
    //   "realloc"
    // };
    // for (std::vector<std::string>::size_type i = 0; i < blacklist.size(); i++)
    //   if (!funcName.compare(0, blacklist[i].size(), blacklist[i]))
    //     continue;

    // HorseFuzz: write function name & hash value to file
    int isDone = 0;
    int cnt_bbs = 0;
    size_t cksum = (size_t) hash32(fileFuncName.c_str(), strlen(fileFuncName.c_str()), 0xa5b35705);

    for (auto &BB : F) {
      BasicBlock::iterator IP = BB.getFirstInsertionPt();
      IRBuilder<> IRB(&(*IP));

      if (getenv("HORSEFUZZ_CG_PROFILING")) {
        for (auto Inst = BB.begin(); Inst != BB.end(); Inst++) {
          Instruction &inst = *Inst;

          if (CallInst* callInst = dyn_cast<CallInst>(&inst)) {
            Function* fcallee = callInst->getCalledFunction();
            if (fcallee != NULL){
              std::string callee = fcallee->getName();
              if(callee.compare(0, 5, "llvm.") == 0)
                continue;
              // HorseFuzz: call the profiling covered functions
              Value *callerName = IRB.CreateGlobalStringPtr(fileFuncName);
              Value *calleeName = IRB.CreateGlobalStringPtr(callee);
              Type *Args[] = {
                Type::getInt8PtrTy(C), // uint8_t *caller
                Type::getInt8PtrTy(C), // uint8_t *callee
              };
              FunctionType *FTy = FunctionType::get(Type::getVoidTy(C), Args, false);
              Constant *funcProfil = M.getOrInsertFunction("llvm_profiling_fcov", FTy);
              IRB.CreateCall(funcProfil, {callerName, calleeName});
            } else {
              nb_indirected_calls++;
            }
          }

          // Clear up profiling at return of the main function
          if (funcName.compare("main") == 0 && isa<ReturnInst>(&inst)) {
            FunctionType *FTy = FunctionType::get(Type::getVoidTy(C), false);
            Constant *funcProfil = M.getOrInsertFunction("llvm_profiling_finish", FTy);
            IRB.CreateCall(funcProfil);
          }
        }
      }

      // HorseFuzz: print information here so that F has some basic blocks
      // It means that F is inside its implementation, not a function call
      if (!isDone) {
        if(!hashset_is_member(funcSet, (void*) cksum)) {
          // SAYF("new fileFuncName: %s, hash value: %u\n", fileFuncName.c_str(), cksum);
          hashset_add(funcSet, (void*) cksum);
          // TODO: remove redundant lines
          outfile << fileFuncName.c_str() << " " << cksum << "\n";
        }
        isDone = 1;
      }

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

      // HorseFuzz: print out functions info (for debugging)
      Value *CkSum = ConstantInt::get(Int32Ty, cksum);
      // Value *MapIdx = IRB.CreateXor(PrevLocCasted, CurLoc);
      // // MapIdx->getType()->dump(); // MapIdx's type i32
      // Type *Args[] = {
      //     Type::getInt32Ty(C), //int map_index
      //     Type::getInt8PtrTy(C), // uint8_t *fileFuncName
      //     Type::getInt32Ty(C) // int cksum
      // };
      // FunctionType *FTy = FunctionType::get(Type::getVoidTy(C), Args, false);
      // Constant *Cst = M.getOrInsertFunction("llvm_profiling_mapidx", FTy);
      // IRB.CreateCall(Cst, {MapIdx, FileFuncName, CkSum});

      /* Update bitmap */

      LoadInst *Counter = IRB.CreateLoad(MapPtrIdx);
      Counter->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
      Value *Incr = IRB.CreateAdd(Counter, ConstantInt::get(Int8Ty, 1));
      IRB.CreateStore(Incr, MapPtrIdx)
          ->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

      // HorseFuzz: afl_funcids_ptr[cur_loc ^ prev_loc] = cksum
      LoadInst *FuncIDPtr = IRB.CreateLoad(AFLFuncIDPtr);
      FuncIDPtr->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
      Value *FuncIDPtrIdx =
          IRB.CreateGEP(FuncIDPtr, IRB.CreateXor(PrevLocCasted, CurLoc));
      LoadInst *Counter1 = IRB.CreateLoad(FuncIDPtrIdx);
      Counter1->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));
      IRB.CreateStore(CkSum, FuncIDPtrIdx)
          ->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

      /* Set prev_loc to cur_loc >> 1 */

      StoreInst *Store =
          IRB.CreateStore(ConstantInt::get(Int32Ty, cur_loc >> 1), AFLPrevLoc);
      Store->setMetadata(M.getMDKindID("nosanitize"), MDNode::get(C, None));

      inst_blocks++;
      cnt_bbs++;

    }
    fb[fileFuncName] = cnt_bbs;
  }

  //outfile2 << file_name.c_str() << ": " << nb_indirected_calls << "\n";

  // Sort functions based on their number of basic blocks
  vector<pair<string, int>> vec;
  map<string, int>::iterator it2;
  for (it2 = fb.begin(); it2 != fb.end(); it2++)
    vec.push_back(make_pair(it2->first, it2->second));
  sort(vec.begin(), vec.end(), sortByVal);
  for (int i = 0; i < (int) vec.size(); i++)
    outfile1 << vec[i].first.c_str() << ": " << vec[i].second << "\n";

  outfile.close();
  outfile1.close();
  //outfile2.close();

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
