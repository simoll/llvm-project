//===-- VEISelLowering.h - VE DAG Lowering Interface ------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file defines the interfaces that VE uses to lower LLVM code into a
// selection DAG.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_LIB_TARGET_VE_VEISELLOWERING_H
#define LLVM_LIB_TARGET_VE_VEISELLOWERING_H

#include "VE.h"
#include "llvm/CodeGen/TargetLowering.h"

namespace llvm {
class VESubtarget;

namespace VEISD {
enum NodeType : unsigned {
  FIRST_NUMBER = ISD::BUILTIN_OP_END,
  CMPICC, // Compare two GPR operands, set icc+xcc.
  CMPFCC, // Compare two FP operands, set fcc.
  BRICC,  // Branch to dest on icc condition
  BRXCC,  // Branch to dest on xcc condition (64-bit only).
  BRFCC,  // Branch to dest on fcc condition
  SELECT,
  SELECT_ICC, // Select between two values using the current ICC flags.
  SELECT_XCC, // Select between two values using the current XCC flags.
  SELECT_FCC, // Select between two values using the current FCC flags.

  EH_SJLJ_SETJMP,         // SjLj exception handling setjmp.
  EH_SJLJ_LONGJMP,        // SjLj exception handling longjmp.
  EH_SJLJ_SETUP_DISPATCH, // SjLj exception handling setup_dispatch.

  Hi,
  Lo, // Hi/Lo operations, typically on a global address.

  FTOI, // FP to Int within a FP register.
  ITOF, // Int to FP within a FP register.
  FTOX, // FP to Int64 within a FP register.
  XTOF, // Int64 to FP within a FP register.

  MAX,
  MIN,
  FMAX,
  FMIN,

  GETFUNPLT,   // load function address through %plt insturction
  GETSTACKTOP, // retrieve address of stack top (first address of
               // locals and temporaries)
  GETTLSADDR,  // load address for TLS access

  MEMBARRIER, // Compiler barrier only; generate a no-op.

  CALL,            // A call instruction.
  RET_FLAG,        // Return with a flag operand.
  GLOBAL_BASE_REG, // Global base reg for PIC.
  FLUSHW,          // FLUSH register windows to stack.

  VEC_BROADCAST, // a scalar value is broadcast across all vector lanes (Operand
                 // 0: the broadcast register)
  VEC_SEQ,       // sequence vector match (Operand 0: the constant stride)

  VEC_VMV,       // custom lowering for vp_vshift

  //// Horizontal operations
  VEC_REDUCE_ANY,
  VEC_POPCOUNT,

  /// Scatter and gather instructions.
  VEC_MSTORE,  // (value, ptr, mask)
  VEC_GATHER,  // (ptrVec, mask),
  VEC_SCATTER, // (value, ptrVec, mask)

  VEC_LVL,

  // Replication on lower/upper32 bit to other half -> I64
  REPL_F32,
  REPL_I32,

  // Internal VVP nodes
#define ADD_VVP_OP(VVP_NAME) VVP_NAME ,
 #include "VVPNodes.inc"

  /// A wrapper node for TargetConstantPool, TargetJumpTable,
  /// TargetExternalSymbol, TargetGlobalAddress, TargetGlobalTLSAddress,
  /// MCSymbol and TargetBlockAddress.
  Wrapper,
};
}

class VETargetLowering : public TargetLowering {
  const VESubtarget *Subtarget;

public:
  VETargetLowering(const TargetMachine &TM, const VESubtarget &STI);

  /// computeKnownBitsForTargetNode - Determine which of the bits specified
  /// in Mask are known to be either zero or one and return them in the
  /// KnownZero/KnownOne bitsets.
  void computeKnownBitsForTargetNode(const SDValue Op, KnownBits &Known,
                                     const APInt &DemandedElts,
                                     const SelectionDAG &DAG,
                                     unsigned Depth = 0) const override;

  MachineBasicBlock *
  EmitInstrWithCustomInserter(MachineInstr &MI,
                              MachineBasicBlock *MBB) const override;

  const char *getTargetNodeName(unsigned Opcode) const override;
  MVT getScalarShiftAmountTy(const DataLayout &, EVT) const override {
    return MVT::i32;
  }

  // inline asm
  ConstraintType getConstraintType(StringRef Constraint) const override;
  ConstraintWeight
  getSingleConstraintMatchWeight(AsmOperandInfo &info,
                                 const char *constraint) const override;
  void LowerAsmOperandForConstraint(SDValue Op, std::string &Constraint,
                                    std::vector<SDValue> &Ops,
                                    SelectionDAG &DAG) const override;

  unsigned getInlineAsmMemConstraint(StringRef ConstraintCode) const override {
    if (ConstraintCode == "o")
      return InlineAsm::Constraint_o;
    return TargetLowering::getInlineAsmMemConstraint(ConstraintCode);
  }

  std::pair<unsigned, const TargetRegisterClass *>
  getRegForInlineAsmConstraint(const TargetRegisterInfo *TRI,
                               StringRef Constraint, MVT VT) const override;

  // scalar ops
  bool isOffsetFoldingLegal(const GlobalAddressSDNode *GA) const override;

  Register getRegisterByName(const char *RegName, LLT VT,
                             const MachineFunction &MF) const override;

  /// Override to support customized stack guard loading.
  bool useLoadStackGuardNode() const override;
  void insertSSPDeclarations(Module &M) const override;

  /// getSetCCResultType - Return the ISD::SETCC ValueType
  EVT getSetCCResultType(const DataLayout &DL, LLVMContext &Context,
                         EVT VT) const override;

  SDValue LowerFormalArguments(SDValue Chain, CallingConv::ID CallConv,
                               bool isVarArg,
                               const SmallVectorImpl<ISD::InputArg> &Ins,
                               const SDLoc &dl, SelectionDAG &DAG,
                               SmallVectorImpl<SDValue> &InVals) const override;
  SDValue LowerFormalArguments_64(SDValue Chain, CallingConv::ID CallConv,
                                  bool isVarArg,
                                  const SmallVectorImpl<ISD::InputArg> &Ins,
                                  const SDLoc &dl, SelectionDAG &DAG,
                                  SmallVectorImpl<SDValue> &InVals) const;
  SDValue LowerCall(TargetLowering::CallLoweringInfo &CLI,
                    SmallVectorImpl<SDValue> &InVals) const override;

  bool CanLowerReturn(CallingConv::ID CallConv, MachineFunction &MF,
                      bool isVarArg,
                      const SmallVectorImpl<ISD::OutputArg> &ArgsFlags,
                      LLVMContext &Context) const override;
  SDValue LowerReturn(SDValue Chain, CallingConv::ID CallConv, bool isVarArg,
                      const SmallVectorImpl<ISD::OutputArg> &Outs,
                      const SmallVectorImpl<SDValue> &OutVals, const SDLoc &dl,
                      SelectionDAG &DAG) const override;
  SDValue withTargetFlags(SDValue Op, unsigned TF, SelectionDAG &DAG) const;
  SDValue makeHiLoPair(SDValue Op, unsigned HiTF, unsigned LoTF,
                       SelectionDAG &DAG) const;
  SDValue makeAddress(SDValue Op, SelectionDAG &DAG) const;

  /// Custom Lower {
  LegalizeAction getActionForExtendedType(unsigned Op, EVT VT) const override {
    return VT.isVector() ? Custom : Expand;
  }

  SDValue LowerOperation(SDValue Op, SelectionDAG &DAG) const override;
  void ReplaceNodeResults(SDNode *N, SmallVectorImpl<SDValue> &Results,
                          SelectionDAG &DAG) const override;
  void LowerOperationWrapper(SDNode *N, SmallVectorImpl<SDValue> &Results,
                             SelectionDAG &DAG) const override;

  SDValue LowerVPToVVP(SDValue Op, SelectionDAG &DAG) const;

  SDValue LowerEXTRACT_SUBVECTOR(SDValue Op, SelectionDAG &DAG) const;
  SDValue LowerVASTART(SDValue Op, SelectionDAG &DAG) const;
  SDValue LowerVAARG(SDValue Op, SelectionDAG &DAG) const;
  SDValue LowerBlockAddress(SDValue Op, SelectionDAG &DAG) const;
  SDValue LowerGlobalAddress(SDValue Op, SelectionDAG &DAG) const;
  SDValue LowerGlobalTLSAddress(SDValue Op, SelectionDAG &DAG) const;
  SDValue LowerToTLSGeneralDynamicModel(SDValue Op, SelectionDAG &DAG) const;
  SDValue LowerToTLSLocalExecModel(SDValue Op, SelectionDAG &DAG) const;
  SDValue LowerConstantPool(SDValue Op, SelectionDAG &DAG) const;

  // SjLj
  SDValue LowerEH_SJLJ_SETJMP(SDValue Op, SelectionDAG &DAG) const;
  SDValue LowerEH_SJLJ_LONGJMP(SDValue Op, SelectionDAG &DAG) const;
  SDValue LowerEH_SJLJ_SETUP_DISPATCH(SDValue Op, SelectionDAG &DAG) const;

  // Custom Operations
  SDValue CreateBroadcast(SDLoc dl, EVT ResTy, SDValue S, SelectionDAG &DAG) const;

  // Vector Operations
  SDValue LowerBUILD_VECTOR(SDValue Op, SelectionDAG &DAG) const;
  SDValue LowerBitcast(SDValue Op, SelectionDAG &DAG) const;
  SDValue LowerVECTOR_SHUFFLE(SDValue Op, SelectionDAG &DAG) const;
  SDValue LowerMGATHER_MSCATTER(SDValue Op, SelectionDAG &DAG) const;
  SDValue LowerMLOAD(SDValue Op, SelectionDAG &DAG) const;
  SDValue LowerMSTORE(SDValue Op, SelectionDAG &DAG) const;
  SDValue LowerEXTRACT_VECTOR_ELT(SDValue Op, SelectionDAG &DAG) const;
  SDValue LowerINSERT_VECTOR_ELT(SDValue Op, SelectionDAG &DAG) const;

  SDValue LowerLOAD(SDValue Op, SelectionDAG &DAG) const;
  SDValue LowerSTORE(SDValue Op, SelectionDAG &DAG) const;
  SDValue LowerVECREDUCE(SDValue Op, SelectionDAG &DAG) const;
  SDValue LowerSETCC(llvm::SDValue, llvm::SelectionDAG &) const;
  SDValue LowerSELECT_CC(llvm::SDValue, llvm::SelectionDAG &) const;
  SDValue LowerVSELECT(llvm::SDValue, llvm::SelectionDAG &) const;
  SDValue LowerTRUNCATE(llvm::SDValue, llvm::SelectionDAG &) const;

  enum class VVPExpansionMode : int8_t {
    ToNextWidth = 0,
    // for use in result type legalization - expand to the next expected result size

    ToNativeWidth = 1
    // for use in LowerOperation -> directly expand to the expanded width
  };

  SDValue ExpandToVVP(SDValue Op, SelectionDAG &DAG, VVPExpansionMode Mode) const;
  // Called in TL::ReplaceNodeResults
  // This replaces the standard ISD node with a VVP VEISD node with a widened
  // result type.

  SDValue LowerToNativeWidthVVP(SDValue Op, SelectionDAG &DAG) const;
  // Called during TL::LowerOperation
  // This replaces this standard ISD node (or VVP VEISD node) with
  // a VVP VEISD node with a native-width type.

  // expand SETCC opernads directly used in vector arithmeticops
  SDValue LowerSETCCInVectorArithmetic(SDValue Op, SelectionDAG &DAG) const;
  // Should we expand the build vector with shuffles?
  bool
  shouldExpandBuildVectorWithShuffles(EVT VT,
                                      unsigned DefinedValues) const override;

  // Other
  SDValue LowerINTRINSIC_VOID(SDValue Op, SelectionDAG &DAG) const;
  SDValue LowerINTRINSIC_W_CHAIN(SDValue Op, SelectionDAG &DAG) const;
  SDValue LowerINTRINSIC_WO_CHAIN(SDValue Op, SelectionDAG &DAG) const;

  SDValue LowerDYNAMIC_STACKALLOC(SDValue Op, SelectionDAG &DAG) const;

  SDValue LowerATOMIC_FENCE(SDValue Op, SelectionDAG &DAG) const;
  SDValue LowerATOMIC_LOAD(SDValue Op, SelectionDAG &DAG) const;
  SDValue LowerATOMIC_STORE(SDValue Op, SelectionDAG &DAG) const;
  SDValue LowerVP_VSHIFT(SDValue Op, SelectionDAG &DAG) const;
  /// } Custom Lower

  bool isFPImmLegal(const APFloat &Imm, EVT VT,
                    bool ForCodeSize) const override;

  bool ShouldShrinkFPConstant(EVT VT) const override {
    // Do not shrink FP constpool if VT == MVT::f128.
    // (ldd, call _Q_fdtoq) is more expensive than two ldds.
    return VT != MVT::f128;
  }

  /// Returns true if the target allows unaligned memory accesses of the
  /// specified type.
  bool allowsMisalignedMemoryAccesses(EVT VT, unsigned AS, unsigned Align,
                                      MachineMemOperand::Flags Flags,
                                      bool *Fast) const override;
  bool mergeStoresAfterLegalization(EVT) const override { return true; }

  bool canMergeStoresTo(unsigned AddressSpace, EVT MemVT,
                        const SelectionDAG &DAG) const override;

  unsigned getJumpTableEncoding() const override;

  const MCExpr *LowerCustomJumpTableEntry(const MachineJumpTableInfo *MJTI,
                                          const MachineBasicBlock *MBB,
                                          unsigned uid,
                                          MCContext &Ctx) const override;

  bool shouldInsertFencesForAtomic(const Instruction *I) const override {
    // VE uses Release consistency, so need fence for each atomics.
    return true;
  }
  Instruction *emitLeadingFence(IRBuilder<> &Builder, Instruction *Inst,
                                AtomicOrdering Ord) const override;
  Instruction *emitTrailingFence(IRBuilder<> &Builder, Instruction *Inst,
                                 AtomicOrdering Ord) const override;

  AtomicExpansionKind
  shouldExpandAtomicRMWInIR(AtomicRMWInst *AI) const override;

  MachineBasicBlock *expandSelectCC(MachineInstr &MI, MachineBasicBlock *BB,
                                    unsigned BROpcode) const;
  MachineBasicBlock *emitEHSjLjSetJmp(MachineInstr &MI,
                                      MachineBasicBlock *MBB) const;
  MachineBasicBlock *emitEHSjLjLongJmp(MachineInstr &MI,
                                       MachineBasicBlock *MBB) const;
  MachineBasicBlock *EmitSjLjDispatchBlock(MachineInstr &MI,
                                           MachineBasicBlock *BB) const;
  void SetupEntryBlockForSjLj(MachineInstr &MI, MachineBasicBlock *MBB,
                              MachineBasicBlock *DispatchBB, int FI) const;
  void finalizeLowering(MachineFunction &MF) const override;

  // VE supports only vector FMA
  bool isFMAFasterThanFMulAndFAdd(const MachineFunction &MF,
                                  EVT VT) const override {
    return VT.isVector();
  }

  /// Return the preferred vector type legalization action.
  LegalizeTypeAction getPreferredVectorAction(MVT VT) const override;
};
} // namespace llvm

#endif // VE_ISELLOWERING_H
