//===-- CustomDAG.h - VE Custom DAG Nodes ------------*- C++ -*-===//
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

#ifndef LLVM_LIB_TARGET_VE_CUSTOMDAG_H
#define LLVM_LIB_TARGET_VE_CUSTOMDAG_H

#include "VE.h"
#include "llvm/CodeGen/TargetLowering.h"
#include "VEISelLowering.h"
#include "llvm/CodeGen/SelectionDAG.h"

namespace llvm {
class VESubtarget;

/// Broadcast, Shuffle, Mask Analysis {
//
enum class BVMaskKind : int8_t {
  Unknown,  // could not infer mask pattern
  Interval, //  interval of all-ones
};

BVMaskKind AnalyzeBuildVectorMask(BuildVectorSDNode *BVN,
                                         unsigned &FirstOne, unsigned &FirstZero,
                                         unsigned &NumElements);

enum class BVKind : int8_t {
  Unknown, // could not infer pattern
  AllUndef, // all lanes undef
  Broadcast, // broadcast 
  Seq,        // (0, .., 255) Sequence 
  SeqBlock,  // (0, .., 15) ^ 16
  BlockSeq,  // 0^16, 1^16, 2^16
};

BVKind AnalyzeBuildVector(BuildVectorSDNode *BVN, unsigned &FirstDef,
                                 unsigned &LastDef, int64_t &Stride,
                                 unsigned &BlockLength, unsigned &NumElements);

/// } Broadcast, Shuffle, Mask Analysis

//// VVP Machinery {
// VVP property queries
Optional<unsigned> GetVVPOpcode(unsigned OpCode);

bool SupportsPackedMode(unsigned Opcode);

bool IsVVPOrVEC(unsigned Opcode);
bool IsVVP(unsigned Opcode);

// Choses the widest element type
EVT getFPConvType(SDNode *Op);

Optional<EVT> getIdiomaticType(SDNode* Op);

VecLenOpt
MinVectorLength(VecLenOpt A, VecLenOpt B);

// Whether direct codegen for this type will result in a packed operation
// (requiring a packed VL param..)
bool
IsPackedType(EVT SomeVT);

// legalize packed-mode broadcasts into lane replication + broadcast
SDValue
LegalizeBroadcast(SDValue Op, SelectionDAG & DAG);

SDValue
LegalizeVecOperand(SDValue Op, SelectionDAG & DAG);

// whether this VVP operation has no mask argument
bool
HasDeadMask(unsigned VVPOC);

VecLenOpt
InferLengthFromMask(SDValue MaskV);

SDValue ReduceVectorLength(SDValue Mask, SDValue DynamicVL, VecLenOpt VLHint,
                           SelectionDAG &DAG);
//// } VVP Machinery

Optional<unsigned> PeekForNarrow(SDValue Op);

Optional<SDValue>
EVLToVal(VecLenOpt Opt, SDLoc &DL, SelectionDAG& DAG);

bool IsMaskType(EVT Ty);
unsigned GetMaskBits(EVT Ty);

// select an appropriate %evl argument for this element count.
// This will return the correct result for packed mode oeprations (half).
unsigned
SelectBoundedVectorLength(unsigned StaticNumElems);

// Packed interpretation sub element
enum class SubElem : int8_t {
  Lo = 0, // integer (63, 32]
  Hi = 1  // float   (32,  0]
};

/// Helper class for short hand custom node creation ///
struct CustomDAG {
  SelectionDAG &DAG;
  SDLoc DL;

  CustomDAG(SelectionDAG &DAG, SDLoc DL) : DAG(DAG), DL(DL) {}

  CustomDAG(SelectionDAG &DAG, SDValue WhereOp) : DAG(DAG), DL(WhereOp) {}

  CustomDAG(SelectionDAG &DAG, SDNode *WhereN) : DAG(DAG), DL(WhereN) {}

  SDValue CreateSeq(EVT ResTy, Optional<SDValue> OpVectorLength) const;

  // create a vector element or scalar bitshift depending on the element type
  // \p ResVT will only be used in case any new node is created
  // dst[i] = src[i + Offset]
  SDValue createElementShift(EVT ResVT, SDValue Src, int Offset,
                             SDValue AVL) const;
  SDValue createScalarShift(EVT ResVT, SDValue Src, int Offset) const;

  SDValue createVMV(EVT ResVT, SDValue SrcV, SDValue OffsetV, SDValue Mask,
                    SDValue Avl) const;

  SDValue getTargetExtractSubreg(MVT SubRegVT, int SubRegIdx,
                                 SDValue RegV) const;

  /// Packed Mode Support {
  SDValue CreateUnpack(EVT DestVT, SDValue Vec, SubElem E, SDValue AVL);

  SDValue CreatePack(EVT DestVT, SDValue LowV, SDValue HighV, SDValue AVL);

  SDValue CreateSwap(EVT DestVT, SDValue V, SDValue AVL);
  /// } Packed Mode Support
  
  /// Mask Insert/Extract {
  SDValue CreateExtractMask(SDValue MaskV, SDValue IndexV) const;
  SDValue CreateInsertMask(SDValue MaskV, SDValue ElemV, SDValue IndexV) const;
  /// } Mask Insert/Extract

  SDValue CreateBroadcast(EVT ResTy, SDValue S,
                          Optional<SDValue> OpVectorLength = None) const;

  // Extract an SX register from a mask
  SDValue createMaskExtract(SDValue MaskV, SDValue Idx);

  // Extract an SX register from a mask
  SDValue createMaskInsert(SDValue MaskV, SDValue Idx, SDValue ElemV);

  SDValue CreateConstMask(unsigned NumElements, bool IsTrue) const;

  /// getNode {
  SDValue getNode(unsigned OC, SDVTList VTL, ArrayRef<SDValue> OpV) const {
    return DAG.getNode(OC, DL, VTL, OpV);
  }

  SDValue getNode(unsigned OC, ArrayRef<EVT> ResVT,
                  ArrayRef<SDValue> OpV) const {
    return DAG.getNode(OC, DL, ResVT, OpV);
  }

  SDValue getNode(unsigned OC, EVT ResVT, ArrayRef<SDValue> OpV) const {
    return DAG.getNode(OC, DL, ResVT, OpV);
  }
  /// } getNode

  SDValue getVectorExtract(SDValue VecV, SDValue IdxV) const {
    assert(VecV.getValueType().isVector());
    auto ElemVT = VecV.getValueType().getVectorElementType();
    return getNode(ISD::EXTRACT_VECTOR_ELT, ElemVT, {VecV, IdxV});
  }

  SDValue getVectorInsert(SDValue DestVecV, SDValue ElemV, SDValue IdxV) const {
    assert(DestVecV.getValueType().isVector());
    return getNode(ISD::INSERT_VECTOR_ELT, DestVecV.getValueType(),
                   {DestVecV, ElemV, IdxV});
  }

  SDValue widenOrNarrow(EVT DestVT, SDValue Op) {
    EVT OpVT = Op.getValueType();
    if (OpVT == DestVT)
      return Op;

    if (!OpVT.isVector())
      return Op;

    return createNarrow(DestVT, Op, OpVT.getVectorNumElements());
  }

  SDValue createNarrow(EVT ResTy, SDValue SrcV, uint64_t NarrowLen) {
    return DAG.getNode(VEISD::VEC_NARROW, DL, ResTy,
                       {SrcV, getConstant(NarrowLen, MVT::i32)});
  }

  EVT getVectorVT(EVT ElemVT, unsigned NumElems) const {
    return EVT::getVectorVT(*DAG.getContext(), ElemVT, NumElems);
  }
  inline SDValue getConstEVL(uint32_t EVL) const { return getConstant(EVL, MVT::i32); }

  SDValue getConstant(uint64_t Val, EVT VT, bool IsTarget = false,
                      bool IsOpaque = false) const;
};

}  // namespace llvm

#endif // LLVM_LIB_TARGET_VE_CUSTOMDAG_H
