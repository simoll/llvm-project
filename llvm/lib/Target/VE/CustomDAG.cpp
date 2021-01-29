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

#include "CustomDAG.h"
#include "VE.h"
#include "VEISelLowering.h"
#include "llvm/CodeGen/SelectionDAG.h"
#include "llvm/CodeGen/TargetLowering.h"
#include "VVPCombine.h"
#include "MaskView.h"

#ifndef DEBUG_TYPE
#define DEBUG_TYPE "customdag"
#endif

namespace llvm {

/// Packing {

template <> Packing getPackingForMaskBits(const LaneBits MB) {
  return Packing::Normal;
}
template <> Packing getPackingForMaskBits(const PackedLaneBits MB) {
  return Packing::Dense;
}

/// } Packing

/// Node Properties {

Optional<unsigned>
inferAVLFromMask(SDValue Mask) {
  if (!Mask) return None;

  std::unique_ptr<MaskView> MV(requestMaskView(Mask.getNode()));
  if (!MV)
    return None;

  unsigned FirstDef, LastDef, NumElems;
  BVMaskKind BVK = AnalyzeBitMaskView(*MV.get(), FirstDef, LastDef, NumElems);
  if (BVK == BVMaskKind::Interval) {
    // FIXME \p FirstDef must be == 0
    return LastDef + 1;
  }

  //
  return Mask.getValueType().getVectorNumElements();
}

SDValue
CustomDAG::inferAVL(SDValue AVL, SDValue Mask, EVT IdiomVT) const {
  if (AVL)
    return AVL;
  auto ConstMaskAVL = inferAVLFromMask(Mask);
  auto ConstTypeAVL = IdiomVT.getVectorNumElements();
  if (!ConstMaskAVL)
    return getConstEVL(ConstTypeAVL);
  return getConstEVL(std::min<unsigned>(ConstTypeAVL, *ConstMaskAVL));
}

PosOpt GetVVPOpcode(unsigned OpCode) {
  if (isVVPOrVEC(OpCode))
    return OpCode;

  switch (OpCode) {
  default:
    return None;

  case ISD::SCALAR_TO_VECTOR:
    return VEISD::VEC_BROADCAST;

  case ISD::SELECT: // additional alias next to VSELECT
    return VEISD::VVP_SELECT;

  case ISD::MLOAD:
    return VEISD::VVP_LOAD;
  case ISD::MSTORE:
    return VEISD::VVP_STORE;

#define HANDLE_VP_TO_VVP(VP_ID, VVP_NAME)                                      \
  case ISD::VP_ID:                                                             \
    return VEISD::VVP_NAME;

#define MAP_VVP_OP(VVP_NAME, NATIVE_ISD)                                       \
  case ISD::NATIVE_ISD:                                                        \
    return VEISD::VVP_NAME;
#include "VVPNodes.def"
  }
}

bool IsVVPUnaryOp(unsigned Opcode) {
  switch (Opcode) {
#define REGISTER_UNARY_VVP_OP(VVP_NAME) case VEISD::VVP_NAME:
#include "VVPNodes.def"
    return true;
  }
  return false;
}

bool IsVVPBinaryOp(unsigned Opcode) {
  switch (Opcode) {
#define REGISTER_BINARY_VVP_OP(VVP_NAME) case VEISD::VVP_NAME:
#include "VVPNodes.def"
    return true;
  }
  return false;
}

bool IsVVPTernaryOp(unsigned Opcode) {
  switch (Opcode) {
#define REGISTER_TERNARY_VVP_OP(VVP_NAME) case VEISD::VVP_NAME:
#include "VVPNodes.def"
    return true;
  }
  return false;
}

bool IsVVPConversionOp(unsigned Opcode) {
  switch (Opcode) {
#define REGISTER_ICONV_VVP_OP(VVP_NAME) case VEISD::VVP_NAME:
#define REGISTER_FPCONV_VVP_OP(VVP_NAME) case VEISD::VVP_NAME:
#include "VVPNodes.def"
    return true;
  }
  return false;
}

bool IsVVPReductionOp(unsigned Opcode) {
  switch (Opcode) {
#define REGISTER_REDUCE_VVP_OP(VVP_NAME) case VEISD::VVP_NAME:
#include "VVPNodes.def"
    return true;
  }
  return false;
}

unsigned getScalarReductionOpcode(unsigned VVPOC, bool IsMask) {
  if (IsMask) {
    switch (VVPOC) {
    case VEISD::VVP_REDUCE_UMIN:
    case VEISD::VVP_REDUCE_SMAX:
    case VEISD::VVP_REDUCE_MUL:
    case VEISD::VVP_REDUCE_AND:
      return ISD::AND;
    case VEISD::VVP_REDUCE_SMIN:
    case VEISD::VVP_REDUCE_UMAX:
    case VEISD::VVP_REDUCE_OR:
      return ISD::OR;
    case VEISD::VVP_REDUCE_ADD:
    case VEISD::VVP_REDUCE_XOR:
      return ISD::XOR;
    default:
      abort();
    }
  }

  // Non i1 reduction Opcode.
  switch (VVPOC) {
#define HANDLE_VVP_REDUCE_TO_SCALAR(VVP_RED_ISD, REDUCE_ISD)                   \
  case VEISD::VVP_RED_ISD:                                                     \
    return ISD::REDUCE_ISD;
#include "VVPNodes.def"
  default:
    break;
  }
  llvm_unreachable("Cannot not scalarize this reduction Opcode!");
}

bool SupportsPackedMode(unsigned Opcode, EVT IdiomVT) {
  bool IsPackedOp = isPackedType(IdiomVT);
  bool IsMaskOp = IdiomVT.getVectorElementType() == MVT::i1;

#if 0
  if (IsMaskOp && IsPackedOp) {
    return false;
  }
#endif

  switch (Opcode) {
  default:
    return false;

  case VEISD::VEC_SEQ:
  case VEISD::VEC_BROADCAST:
    return true;
#define REGISTER_PACKED(VVP_NAME)                                              \
  case VEISD::VVP_NAME:                                                        \
    return IsPackedOp;
#include "VVPNodes.def"
  }
}

#define IF_IN_VEISD_RANGE(STARTOC, ENDOC)                                      \
  if ((VEISD::STARTOC <= OC) && (OC <= VEISD::ENDOC))

bool isVVPOrVEC(unsigned OC) {
  IF_IN_VEISD_RANGE(VEC_FIRST, VEC_LAST) { return true; }
  IF_IN_VEISD_RANGE(VM_FIRST, VM_LAST) { return true; }

  return IsVVP(OC);
}
#undef IF_IN_VEISD_RANGE

bool IsVVP(unsigned Opcode) {
  switch (Opcode) {
  default:
    return false;
#define REGISTER_VVP_OP(VVP_NAME)                                              \
  case VEISD::VVP_NAME:                                                        \
    return true;
#include "VVPNodes.def"
  }
}

// Return the mask operand position for this VVP or VEC op.
Optional<int> getAVLPos(unsigned Opc) {
  // This is only available for VP SDNodes
  auto PosOpt = ISD::getVPExplicitVectorLengthIdx(Opc);
  if (PosOpt)
    return *PosOpt;

  // VEC Opcodes and special cases.
  switch (Opc) {
  case VEISD::VEC_SEQ:
    return 0;
  case VEISD::VEC_BROADCAST:
    return 1;
  }

  // VVP Opcodes.
  if (IsVVP(Opc)) {
    auto MaskOpt = getMaskPos(Opc);
    if (!MaskOpt)
      return None;
    return *MaskOpt + 1;
  }
  return None;
}

SDValue getNodeAVL(SDValue Op) {
  auto PosOpt = getAVLPos(Op->getOpcode());
  return PosOpt ? Op->getOperand(*PosOpt) : SDValue();
}

// Return the AVL operand position for this VVP Op.
Optional<int> getMaskPos(unsigned Opc) {
  auto PosOpt = ISD::getVPMaskIdx(Opc);
  if (PosOpt)
    return *PosOpt;

  // Selection mask.
  if (Opc == ISD::VSELECT || Opc == ISD::SELECT) {
    return 0;
  }

  switch (Opc) {
  case VEISD::VVP_SELECT:
    return 2;
  case VEISD::VVP_LOAD:
    return 3;
  case VEISD::VVP_STORE:
    return 4;
  case VEISD::VVP_GATHER:
    return 1;
  case VEISD::VVP_SCATTER:
    return 2;
  }

  if (IsVVPUnaryOp(Opc) || IsVVPConversionOp(Opc))
    return 1;
  if (IsVVPBinaryOp(Opc))
    return 2;
  if (IsVVPTernaryOp(Opc))
    return 3;
  if (IsVVPReductionOp(Opc))
    return *getReductionVectorParamPos(Opc) + 1;
  return None;
}

SDValue getNodeMask(SDValue Op) {
  auto PosOpt = getMaskPos(Op->getOpcode());
  return PosOpt ? Op->getOperand(*PosOpt) : SDValue();
}

// Choses the widest element type
EVT getLargestConvType(SDNode *Op) {
  EVT ResVT = Op->getValueType(0);
  EVT OpVT = Op->getOperand(0).getValueType();
  return ResVT.getStoreSizeInBits() > OpVT.getStoreSizeInBits() ? ResVT : OpVT;
}

PosOpt getVVPReductionStartParamPos(unsigned VVPOC) {
  switch (VVPOC) {
  case VEISD::VVP_REDUCE_SEQ_FADD:
  case VEISD::VVP_REDUCE_SEQ_FMUL:
    return 0;
  default:
    return None;
  }
}

PosOpt getVPReductionVectorParamPos(unsigned VPISD) {
  PosOpt VecPos;
  switch (VPISD) {
  default:
    break;
#define BEGIN_REGISTER_VP_SDNODE(VPISD, ...) case ISD::VPISD:
#define HANDLE_VP_REDUCTION(ACCUPOS, VECTORPOS, ...) VecPos = VECTORPOS;
#define END_REGISTER_VP_SDNODE(VPISD) break;
#include "llvm/IR/VPIntrinsics.def"
  }
  return VecPos;
}

PosOpt getIntrinReductionVectorParamPos(unsigned ISD) {
  switch (ISD) {
  case ISD::VECREDUCE_ADD:
  case ISD::VECREDUCE_MUL:
  case ISD::VECREDUCE_AND:
  case ISD::VECREDUCE_OR:
  case ISD::VECREDUCE_XOR:
  case ISD::VECREDUCE_UMIN:
  case ISD::VECREDUCE_UMAX:
  case ISD::VECREDUCE_SMIN:
  case ISD::VECREDUCE_SMAX:
  case ISD::VECREDUCE_FADD:
  case ISD::VECREDUCE_FMUL:
  case ISD::VECREDUCE_FMIN:
  case ISD::VECREDUCE_FMAX:
    return 0;

  case ISD::VECREDUCE_SEQ_FADD:
  case ISD::VECREDUCE_SEQ_FMUL:
    return 1;
  }
  return None;
}

PosOpt getVVPReductionVectorParamPos(unsigned VVPOpcode) {
  if (!IsVVPReductionOp(VVPOpcode))
    return None;

  PosOpt StartPosOpt = getVVPReductionStartParamPos(VVPOpcode);
  if (!StartPosOpt)
    return 0;
  return *StartPosOpt + 1;
}

PosOpt getReductionVectorParamPos(unsigned ISD) {
  // VP reduction param pos
  PosOpt VecPos = getVPReductionVectorParamPos(ISD);
  if (VecPos)
    return VecPos;

  // VVP reduction
  VecPos = getVVPReductionVectorParamPos(ISD);
  if (VecPos)
    return VecPos;

  // Regular reduction
  VecPos = getIntrinReductionVectorParamPos(ISD);
  return VecPos;
}

/// } Node Properties

Optional<unsigned> GetVVPForVP(unsigned VPOC) {
  switch (VPOC) {
#define HANDLE_VP_TO_VVP(VP_ISD, VVP_VEISD)                                    \
  case ISD::VP_ISD:                                                            \
    return VEISD::VVP_VEISD;
#include "VVPNodes.def"

  default:
    return None;
  }
}

Optional<EVT> getIdiomaticType(SDNode *Op) {
  // For reductions -> the reduced vector type
  PosOpt RedVecPos = getReductionVectorParamPos(Op->getOpcode());
  if (RedVecPos)
    return Op->getOperand(RedVecPos.getValue())->getValueType(0);

  // Otw, translate everyhing to VVP (expect the VP and non-VP characteristic
  // parameter to be at the same position)
  unsigned OC = Op->getOpcode();
  switch (OC) {
  default:
    break;
#define HANDLE_VP_TO_VVP(VP_ID, VVP_ID)                                        \
  case ISD::VP_ID:                                                             \
    OC = VEISD::VVP_ID;                                                        \
    break;
#include "VVPNodes.def"
  }

  // Expect VEISD:: VVP or ISD::non-VP Opcodes here
  switch (OC) {
  default:
    // For memory ops -> the transfered data type
    if (auto MemN = dyn_cast<MemSDNode>(Op))
      return MemN->getMemoryVT();
    return None;

  case ISD::SELECT: // not aliased with VVP_SELECT
  case ISD::CONCAT_VECTORS:
  case ISD::EXTRACT_SUBVECTOR:
  case ISD::VECTOR_SHUFFLE:
  case ISD::BUILD_VECTOR:
  case ISD::SCALAR_TO_VECTOR:
    return Op->getValueType(0);

    // Known VP ops
    // all standard un/bin/tern-ary operators
#define ADD_UNARY_VVP_OP(VVP_NAME, NATIVE_ISD)                                 \
  case VEISD::VVP_NAME:                                                        \
  case ISD::NATIVE_ISD:
#define ADD_BINARY_VVP_OP(VVP_NAME, NATIVE_ISD)                                \
  case VEISD::VVP_NAME:                                                        \
  case ISD::NATIVE_ISD:
#define ADD_TERNARY_VVP_OP(VVP_NAME, NATIVE_ISD)                               \
  case VEISD::VVP_NAME:                                                        \
  case ISD::NATIVE_ISD:
#include "VVPNodes.def"
    return Op->getValueType(0);

#define ADD_FPCONV_VVP_OP(VVP_NAME, NATIVE_ISD)                                \
  case VEISD::VVP_NAME:                                                        \
  case ISD::NATIVE_ISD:
#define ADD_ICONV_VVP_OP(VVP_NAME, NATIVE_ISD)                                 \
  case VEISD::VVP_NAME:                                                        \
  case ISD::NATIVE_ISD:
#include "VVPNodes.def"
    return getLargestConvType(Op);

  case VEISD::VEC_TOMASK:
  case VEISD::VEC_NARROW:
  case VEISD::VEC_SEQ:
  case VEISD::VEC_BROADCAST:
    return Op->getValueType(0);

  case VEISD::VVP_LOAD:
  case VEISD::VVP_GATHER:
    return Op->getValueType(0);

  case VEISD::VVP_STORE:
  case VEISD::VVP_SCATTER:
    return Op->getOperand(1)->getValueType(0);
  }
}

VecLenOpt MinVectorLength(VecLenOpt A, VecLenOpt B) {
  if (!A)
    return B;
  if (!B)
    return A;
  return std::min<unsigned>(A.getValue(), B.getValue());
}

EVT splitType(LLVMContext &Ctx, EVT PackedVT, PackElem P) {
  assert(isPackedType(PackedVT));
  unsigned PackedNumEls = PackedVT.getVectorNumElements();

  unsigned OneExtra = P == PackElem::Hi ? PackedNumEls % 2 : 0;
  return EVT::getVectorVT(Ctx, PackedVT.getVectorElementType(),
                          (PackedNumEls / 2) + OneExtra);
}

// Whether direct codegen for this type will result in a packed operation
// (requiring a packed VL param..)

bool isPackedType(EVT SomeVT) {
  if (!SomeVT.isVector())
    return false;
  return SomeVT.getVectorNumElements() > StandardVectorWidth;
}

// legalize packed-mode broadcasts into lane replication + broadcast
static SDValue LegalizeBroadcast(SDValue Op, SelectionDAG &DAG) {
  if (Op.getOpcode() != VEISD::VEC_BROADCAST)
    return Op;

  EVT VT = Op.getValueType();
  SDLoc DL(Op);

  auto ScaOp = Op.getOperand(0);
  auto ScaTy = ScaOp->getValueType(0);
  auto VLOp = Op.getOperand(1);

  // v256x broadcast (element has to be i64/f64 always)
  if (!isPackedType(VT))
    return Op;

  LLVM_DEBUG(dbgs() << "Legalize packed broadcast\n");

  // v512x broadcast
  // This is a packed broadcast.
  // replicate the scalar sub reg (f32 or i32) onto the opposing half of the
  // scalar reg and feed it into a I64 -> v256i64 broadcast.
  unsigned ReplOC;
  if (ScaTy == MVT::f32) {
    ReplOC = VEISD::REPL_F32;
  } else if (ScaTy == MVT::i32) {
    ReplOC = VEISD::REPL_I32;
  } else {
    // This could either be an over-packed broadcast (i64 or f64) or a proper
    // packed broadcast with element replication.
    assert((ScaTy == MVT::i64) || (ScaTy == MVT::f64));
    LLVM_DEBUG(dbgs() << "already using I64 -> unchanged!\n");
    return Op;
  }

  auto ReplOp = DAG.getNode(ReplOC, DL, MVT::i64, ScaOp);
  // auto LegalVecTy = MVT::getVectorVT(MVT::i64, Ty.getVectorNumElements());
  return DAG.getNode(VEISD::VEC_BROADCAST, DL, VT, {ReplOp, VLOp});
}

bool isMaskType(EVT VT) {
  if (!VT.isVector())
    return false;

  // an actual bit mask type
  if (VT.getVectorElementType() == MVT::i1)
    return true;

  // not a mask
  return false;
}

bool IsAllTrueMask(SDValue Op) {
  if (!isMaskType(Op.getValueType()))
    return false;
  auto SplatV = getSplatValue(Op.getNode());
  if (!SplatV) {
    // FIXME: Could already be a broadcast.
    return false;
  }
  if (auto ConstSD = dyn_cast<ConstantSDNode>(SplatV)) {
    return ConstSD->getSExtValue() != 0;
  }
  return false;
}

// whether this VVP operation has no mask argument
bool HasDeadMask(unsigned VVPOC) {
  switch (VVPOC) {
  default:
    return false;

  case VEISD::VVP_LOAD:
    return true;
  }
}

#if 0
#endif

Optional<unsigned> PeekForNarrow(SDValue Op) {
  if (!Op.getValueType().isVector())
    return None;
  if (Op->use_size() != 1)
    return None;
  auto OnlyN = *Op->use_begin();
  if (OnlyN->getOpcode() != VEISD::VEC_NARROW)
    return None;
  return cast<ConstantSDNode>(OnlyN->getOperand(1))->getZExtValue();
}

Optional<SDValue> EVLToVal(VecLenOpt Opt, SDLoc &DL, SelectionDAG &DAG) {
  if (!Opt)
    return None;
  return DAG.getConstant(Opt.getValue(), DL, MVT::i32);
}

bool isOverPackedType(EVT VT) {
  if (!VT.isVector())
    return false;
  if (VT.getVectorElementType() != MVT::i64 &&
      VT.getVectorElementType() != MVT::f64)
    return false;
  return VT.getVectorNumElements() > StandardVectorWidth;
}

unsigned GetMaskBits(EVT VT) {
  if (!VT.isVector())
    return 0;

  EVT ElemVT = VT.getVectorElementType();
  if (!ElemVT.isInteger())
    return 0;

  return ElemVT.getScalarSizeInBits() * VT.getVectorNumElements();
}

// select an appropriate %evl argument for this element count.
// This will return the correct result for packed mode oeprations (half).
unsigned SelectBoundedVectorLength(unsigned StaticNumElems) {
  if (StaticNumElems > StandardVectorWidth) {
    return (StaticNumElems + 1) / 2;
  }
  return StaticNumElems;
}

/// class CustomDAG {

/// Helper class for short hand custom node creation ///
SDValue CustomDAG::CreateSeq(EVT ResTy,
                             Optional<SDValue> OpVectorLength) const {
  // Pick VL
  SDValue VectorLen;
  if (OpVectorLength.hasValue()) {
    VectorLen = OpVectorLength.getValue();
  } else {
    VectorLen = DAG.getConstant(
        SelectBoundedVectorLength(ResTy.getVectorNumElements()), DL, MVT::i32);
  }

  return DAG.getNode(VEISD::VEC_SEQ, DL, ResTy, VectorLen);
}

SDValue CustomDAG::getTargetExtractSubreg(MVT SubRegVT, int SubRegIdx,
                                          SDValue RegV) const {
  return DAG.getTargetExtractSubreg(SubRegIdx, DL, SubRegVT, RegV);
}

// create a vector element or scalar bitshift depending on the element type
// dst[i] = src[i + Offset]
SDValue CustomDAG::createScalarShift(EVT ResVT, SDValue Src, int Offset) const {
  if (Offset == 0)
    return Src;
  unsigned OC = Offset > 0 ? ISD::SHL : ISD::SRL; // VE::SLLri : VE::SRLri;
  SDValue ShiftV = getConstant(std::abs(Offset),
                               MVT::i32); // This is the ShiftAmount constant
  return DAG.getNode(OC, DL, ResVT, Src, ShiftV);
}

// create a vector element or scalar bitshift depending on the element type
// dst[i] = src[i + Offset]
SDValue CustomDAG::createElementShift(EVT ResVT, SDValue Src, int Offset,
                                      SDValue AVL) const {
  if (Offset == 0)
    return Src;

  // scalar bit shift
  if (!Src.getValueType().isVector()) {
    return createScalarShift(ResVT, Src, Offset);
  }

  assert(ResVT.getVectorNumElements() <= 256 && "TODO implement packed mode");

  // vector shift
  EVT VecVT = Src.getValueType();
  assert(!isPackedType(VecVT) && "TODO implement");
  assert(!isMaskType(VecVT));
  return createVMV(ResVT, Src, getConstant(Offset, MVT::i32),
                   createUniformConstMask(Packing::Normal,
                                          VecVT.getVectorNumElements(), true),
                   AVL);
}

SDValue CustomDAG::createPassthruVMV(EVT ResVT, SDValue SrcV, SDValue OffsetV,
                                     SDValue Mask, SDValue PassthruV,
                                     SDValue Avl) const {
  abort(); // TODO return DAG.getNode(VEISD::VEC_VMV, DL, ResVT, {SrcV, OffsetV,
           // Mask, Avl});
}

SDValue CustomDAG::createVMV(EVT ResVT, SDValue SrcV, SDValue OffsetV,
                             SDValue Mask, SDValue Avl) const {
  return DAG.getNode(VEISD::VEC_VMV, DL, ResVT, {SrcV, OffsetV, Mask, Avl});
}

SDValue CustomDAG::CreateExtractMask(SDValue MaskV, SDValue IndexV) const {
  return DAG.getNode(VEISD::VM_EXTRACT, DL, MVT::i64, MaskV, IndexV);
}

SDValue CustomDAG::CreateInsertMask(SDValue MaskV, SDValue ElemV,
                                    SDValue IndexV) const {
  return DAG.getNode(VEISD::VM_INSERT, DL, MaskV.getValueType(), MaskV, ElemV,
                     IndexV);
}

SDValue CustomDAG::CreateMaskPopcount(SDValue MaskV, SDValue AVL) const {
  return DAG.getNode(VEISD::VM_POPCOUNT, DL, MVT::i64, MaskV, AVL);
}

static SDValue foldUnpackFromPack(SDValue PackOp, PackElem Part, EVT DestVT) {
  if (PackOp->getOpcode() != VEISD::VEC_PACK)
    return SDValue();

  // Check for implicit swapping.
  // The following unpack of pack are foldable (they are noop):
  //   Any mask unpack.
  // Or:
  //   Any over-packed unpack.
  // Or:
  // v256i32 vec_unpack_lo SrcV
  // v256f32 vec_unpack_hi SrcV
  EVT SrcVT = PackOp.getValueType();
  PackElem DestPart = getPackElemForVT(DestVT);
  if (!isMaskType(SrcVT) && !isOverPackedType(SrcVT) && (DestPart != Part))
    return SDValue();

  if (Part == PackElem::Lo)
    return PackOp->getOperand(0);
  else
    return PackOp->getOperand(1);
}

static SDValue foldUnpackFromBroadcast(SDValue Vec, PackElem Part, EVT DestVT,
                                       SDValue AVL, const CustomDAG &CDAG) {
  SDValue Scalar = getSplatValue(Vec.getNode());
  if (!Scalar)
    return SDValue();

  // Fold unpack from an overpacked or mask broadcast.
  if (isOverPackedType(Vec.getValueType()) || isMaskType(Vec.getValueType()))
    return CDAG.CreateBroadcast(DestVT, Scalar, AVL);

  // Fold unpack from broadcast from replication.
  if (SDValue Simplified = combineUnpackLoHi(Vec, Part, DestVT, AVL, CDAG))
    return Simplified;

  return SDValue();
}

SDValue CustomDAG::CreateUnpack(EVT DestVT, SDValue Vec, PackElem E,
                                SDValue AVL) const {
  if (SDValue SimplifiedV = foldUnpackFromBroadcast(Vec, E, DestVT, AVL, *this))
    return SimplifiedV;
  // Immediately fold unpack from pack.
  if (SDValue PackedV = foldUnpackFromPack(Vec, E, DestVT))
    return PackedV;

  unsigned OC = getUnpackOpcodeForPart(E);
  return DAG.getNode(OC, DL, DestVT, Vec, AVL);
}

SDValue CustomDAG::CreatePack(EVT DestVT, SDValue LowV, SDValue HighV,
                              SDValue AVL) const {
  // TODO Peek through paired unpacks!
  return DAG.getNode(VEISD::VEC_PACK, DL, DestVT, LowV, HighV, AVL);
}

SDValue CustomDAG::CreateSwap(EVT DestVT, SDValue V, SDValue AVL) const {
  return DAG.getNode(VEISD::VEC_SWAP, DL, DestVT, V, AVL);
}

SDValue CustomDAG::CreateBroadcast(EVT ResTy, SDValue S,
                                   Optional<SDValue> OpVectorLength) const {

  // Pick VL
  SDValue VectorLen;
  if (OpVectorLength.hasValue()) {
    VectorLen = OpVectorLength.getValue();
  }
  if (!OpVectorLength.hasValue() || !VectorLen) {
    VectorLen = DAG.getConstant(
        SelectBoundedVectorLength(ResTy.getVectorNumElements()), DL, MVT::i32);
  }

  // FIXME legalize vlen for packed mode!

  // Over-packed case: immediately split this into double packing.
  if (isOverPackedType(ResTy)) {
    MVT LegalPartVT = getUnpackSourceType(ResTy, PackElem::Lo);
    auto PartV = LegalizeBroadcast(
        DAG.getNode(VEISD::VEC_BROADCAST, DL, LegalPartVT, {S, VectorLen}),
        DAG);
    return CreatePack(ResTy, PartV, PartV, VectorLen);
  }

  // Non-mask case
  if (ResTy.getVectorElementType() != MVT::i1) {
    return LegalizeBroadcast(
        DAG.getNode(VEISD::VEC_BROADCAST, DL, ResTy, {S, VectorLen}), DAG);
  }

  // Mask bit broadcast
  auto BcConst = dyn_cast<ConstantSDNode>(S);

  // Constant mask splat
  if (BcConst) {
    return createUniformConstMask(getPackingForVT(ResTy),
                                  ResTy.getVectorNumElements(),
                                  BcConst->getSExtValue() != 0);
  }

  // Generic mask code path
  auto BoolTy = S.getSimpleValueType();
  assert(BoolTy == MVT::i32);

  // cast to i32 ty
  SDValue CmpElem = DAG.getSExtOrTrunc(S, DL, MVT::i32);

  unsigned ElemCount = ResTy.getVectorNumElements();
  MVT CmpVecTy = MVT::getVectorVT(BoolTy, ElemCount);

  // broadcast to vector
  SDValue BCVec =
      DAG.getNode(VEISD::VEC_BROADCAST, DL, CmpVecTy, {CmpElem, VectorLen});
  SDValue ZeroVec =
      CreateBroadcast(CmpVecTy, {DAG.getConstant(0, DL, BoolTy)}, VectorLen);

  MVT BoolVecTy = MVT::getVectorVT(MVT::i1, ElemCount);

  // broadcast(Data) != broadcast(0)
  return DAG.getSetCC(DL, BoolVecTy, BCVec, ZeroVec, ISD::CondCode::SETNE);
}

// Extract an SX register from a mask
SDValue CustomDAG::createMaskExtract(SDValue MaskV, SDValue Idx) const {
  return DAG.getNode(VEISD::VM_EXTRACT, DL, MVT::i64, {MaskV, Idx});
}

// Extract an SX register from a mask
SDValue CustomDAG::createMaskInsert(SDValue MaskV, SDValue Idx,
                                    SDValue ElemV) const {
  return DAG.getNode(VEISD::VM_INSERT, DL, MaskV.getValueType(),
                     {MaskV, Idx, ElemV});
}

template <typename MaskBits>
SDValue CustomDAG::createConstMask(unsigned NumElems,
                                   const MaskBits &TrueBits) const {
  Packing Packing = getPackingForMaskBits<>(TrueBits);

  // Scan for trivial cases
  bool TrivialMask = true;
  for (unsigned i = 1; i < NumElems; ++i) {
    if (TrueBits[i] != TrueBits[0]) {
      TrivialMask = false;
      break;
    }
  }
  if (TrivialMask) {
    return createUniformConstMask(Packing, TrueBits.size(), TrueBits[0]);
  }

  SDValue MaskV = createUniformConstMask(Packing, TrueBits.size(), false);
  unsigned RegPartIdx = 0;
  for (unsigned StartIdx = 0; StartIdx < NumElems;
       StartIdx += SXRegSize, ++RegPartIdx) {
    uint64_t ConstReg = 0;
    for (uint i = 0; i < SXRegSize; ++i) {
      uint64_t LaneMask = ((uint64_t)1) << i;
      ConstReg |= TrueBits[StartIdx + i] ? LaneMask : 0;
    }
    // initial mask is all-zero already
    if (!ConstReg)
      continue;

    MaskV = createMaskInsert(MaskV, getConstant(RegPartIdx, MVT::i32),
                             getConstant(ConstReg, MVT::i64));
  }
  return MaskV;
}

template SDValue CustomDAG::createConstMask<LaneBits>(unsigned,
                                                      const LaneBits &) const;
template SDValue
CustomDAG::createConstMask<PackedLaneBits>(unsigned,
                                           const PackedLaneBits &) const;

SDValue CustomDAG::createSelect(EVT ResVT, SDValue OnTrueV, SDValue OnFalseV,
                                SDValue MaskV, SDValue PivotV) const {
  if (OnTrueV.isUndef())
    return OnFalseV;
  if (OnFalseV.isUndef())
    return OnTrueV;

  return DAG.getNode(VEISD::VVP_SELECT, DL, ResVT,
                     {OnTrueV, OnFalseV, MaskV, PivotV});
}

SDValue CustomDAG::createUniformConstMask(Packing Packing, unsigned NumElements,
                                          bool IsTrue) const {
  auto MaskVT = getMaskVT(Packing);

  // VEISelDAGtoDAG will replace this with the constant-true VM
  auto TrueVal = DAG.getConstant(-1, DL, MVT::i32);

#if 0
  // AVL legalization happens during lowering.
  unsigned AVL = NumElements;
  if (Packing == Packing::Dense) {
    AVL = (NumElements + 1) / 2;
  }
#endif

  auto Res = getNode(VEISD::VEC_BROADCAST, MaskVT,
                     {TrueVal, getConstEVL(NumElements)});
  if (IsTrue)
    return Res;

  return DAG.getNOT(DL, Res, Res.getValueType());
}

SDValue CustomDAG::getConstant(uint64_t Val, EVT VT, bool IsTarget,
                               bool IsOpaque) const {
  return DAG.getConstant(Val, DL, VT, IsTarget, IsOpaque);
}

void CustomDAG::dumpValue(SDValue V) const { V->print(dbgs(), &DAG); }

SDValue CustomDAG::getVectorExtract(SDValue VecV, SDValue IdxV) const {
  assert(VecV.getValueType().isVector());
  auto ElemVT = VecV.getValueType().getVectorElementType();
  return getNode(ISD::EXTRACT_VECTOR_ELT, ElemVT, {VecV, IdxV});
}

SDValue CustomDAG::getVectorInsert(SDValue DestVecV, SDValue ElemV,
                                   SDValue IdxV) const {
  assert(DestVecV.getValueType().isVector());
  return getNode(ISD::INSERT_VECTOR_ELT, DestVecV.getValueType(),
                 {DestVecV, ElemV, IdxV});
}

SDValue CustomDAG::createMaskCast(SDValue VectorV, SDValue AVL) const {
  if (isMaskType(VectorV.getValueType()))
    return VectorV;

  if (isPackedType(VectorV.getValueType())) {
    auto ValVT = VectorV.getValueType();
    auto LoPart = CreateUnpack(getSplitVT(ValVT), VectorV, PackElem::Lo, AVL);
    auto HiPart = CreateUnpack(getSplitVT(ValVT), VectorV, PackElem::Hi, AVL);
    auto LoMask = createMaskCast(LoPart, AVL);
    auto HiMask = createMaskCast(HiPart, AVL);
    const auto PackedMaskVT = MVT::v512i1;
    return CreatePack(PackedMaskVT, LoMask, HiMask, AVL);
  }

  return DAG.getNode(VEISD::VEC_TOMASK, DL, getMaskVTFor(VectorV),
                     {VectorV, AVL});
}

EVT CustomDAG::legalizeVectorType(SDValue Op, VVPExpansionMode Mode) const {
  return VLI.LegalizeVectorType(Op->getValueType(0), Op, DAG, Mode);
}

SDValue CustomDAG::getTokenFactor(ArrayRef<SDValue> Tokens) const {
  return DAG.getNode(ISD::TokenFactor, DL, MVT::Other, Tokens);
}

SDValue CustomDAG::getVVPLoad(EVT LegalResVT, SDValue Chain, SDValue PtrV,
                              SDValue StrideV, SDValue MaskV,
                              SDValue AVL) const {
  return DAG.getNode(VEISD::VVP_LOAD, DL, {LegalResVT, MVT::Other},
                     {Chain, PtrV, StrideV, MaskV, AVL});
}

SDValue CustomDAG::getVVPStore(SDValue Chain, SDValue DataV, SDValue PtrV,
                               SDValue StrideV, SDValue MaskV,
                               SDValue AVL) const {
  return DAG.getNode(VEISD::VVP_LOAD, DL, MVT::Other,
                     {Chain, DataV, PtrV, StrideV, MaskV, AVL});
}

SDValue CustomDAG::getVVPGather(EVT LegalResVT, SDValue ChainV, SDValue PtrV,
                                SDValue MaskV, SDValue AVL) const {
  return DAG.getNode(VEISD::VVP_GATHER, DL, {LegalResVT, MVT::Other},
                     {ChainV, PtrV, MaskV, AVL});
}

SDValue CustomDAG::extractPackElem(SDValue Op, PackElem Part, SDValue AVL) {
  EVT OldValVT = Op.getValue(0).getValueType();
  if (!OldValVT.isVector())
    return Op;

  // TODO peek through pack operations
  return CreateUnpack(getSplitVT(OldValVT), Op, Part, AVL);
}

SDValue CustomDAG::createConstantTargetMask(VVPWideningInfo WidenInfo) const {
  /// Use the eventual native vector width for all newly generated operands
  // we do not want to go through ::ReplaceNodeResults again only to have them
  // widened
  unsigned NativeVectorWidth =
      WidenInfo.PackedMode ? PackedWidth : StandardVectorWidth;

  // Generate a remainder mask for packed operations
  Packing PackFlag = WidenInfo.PackedMode ? Packing::Dense : Packing::Normal;
  if (!WidenInfo.NeedsPackedMasking) {
    return createUniformConstMask(PackFlag, NativeVectorWidth, true);

  } else {
    // TODO only really generate a mask if there is a change the operation will
    // benefit from it (eg, for vfdiv)
    PackedLaneBits MaskBits;
    MaskBits.reset();
    MaskBits.flip();
    size_t OddRemainderBitPos = WidenInfo.ActiveVectorLength;
    MaskBits[OddRemainderBitPos] = false;
    return createConstMask<>(PackedWidth, MaskBits);
  }
}

SDValue CustomDAG::createTargetAVL(VVPWideningInfo WidenInfo) const {
  // Legalize the AVL
  if (WidenInfo.PackedMode) {
    return getConstEVL((WidenInfo.ActiveVectorLength + 1) / 2);
  } else {
    return getConstEVL(WidenInfo.ActiveVectorLength);
  }
}

CustomDAG::TargetMasks
CustomDAG::createTargetSplitMask(VVPWideningInfo WidenInfo, SDValue RawMask,
                                 SDValue RawAVL, PackElem Part) {
  // No masking caused, we simply adjust the AVL for the parts
  SDValue NewAVL;
  if (!RawAVL) {
    unsigned PartAVL = WidenInfo.ActiveVectorLength / 2;
    if (WidenInfo.NeedsPackedMasking) {
      PartAVL += (int)(Part == PackElem::Lo);
    }
    NewAVL = getConstEVL(PartAVL);
  } else if (WidenInfo.NeedsPackedMasking) {
    if (Part == PackElem::Lo) {
      auto PlusOne = getNode(ISD::ADD, MVT::i32, {RawAVL, getConstEVL(1)});
      NewAVL = getNode(ISD::SRL, MVT::i32, {PlusOne, getConstEVL(1)});
    } else {
      NewAVL = getNode(ISD::SRL, MVT::i32, {RawAVL, getConstEVL(1)});
    }
  } else {
    NewAVL = getNode(ISD::SRL, MVT::i32, {RawAVL, getConstEVL(1)});
  }

  // Legalize Mask (unpack or all-true)
  SDValue NewMask;
  if (!RawMask) {
    NewMask = createUniformConstMask(Packing::Normal, true);
  } else {
    NewMask = extractPackElem(RawMask, Part, NewAVL);
  }

  return CustomDAG::TargetMasks(NewMask, NewAVL);
}

CustomDAG::TargetMasks CustomDAG::createTargetMask(VVPWideningInfo WidenInfo,
                                                   SDValue RawMask,
                                                   SDValue RawAVL) {
  bool IsDynamicAVL = RawAVL && !isa<ConstantSDNode>(RawAVL);

  // Legalize AVL
  SDValue NewAVL;
  if (!RawAVL) {
    NewAVL = createTargetAVL(WidenInfo);
  } else if (auto ConstAVL = dyn_cast<ConstantSDNode>(RawAVL)) {
    WidenInfo.ActiveVectorLength = std::min<unsigned>(
        ConstAVL->getZExtValue(), WidenInfo.ActiveVectorLength);
    NewAVL = createTargetAVL(WidenInfo);
  } else if (RawAVL && !WidenInfo.PackedMode) {
    NewAVL = RawAVL;
  } else {
    assert(WidenInfo.PackedMode);
    assert(IsDynamicAVL);

    auto PlusOne = getNode(ISD::ADD, MVT::i32, {RawAVL, getConstEVL(1)});
    NewAVL = getNode(ISD::SRL, MVT::i32, {PlusOne, getConstEVL(1)});
  }

  // Legalize Mask (nothing to do here)
  SDValue NewMask;
  if (!RawMask) {
    NewMask = createConstantTargetMask(WidenInfo);
  } else {
    NewMask = RawMask;
  }

  return CustomDAG::TargetMasks(NewMask, NewAVL);
}

SDValue CustomDAG::getTargetInsertSubreg(int SRIdx, EVT VT, SDValue Operand,
                                         SDValue SubReg) const {
  return DAG.getTargetInsertSubreg(SRIdx, DL, VT, Operand, SubReg);
}

SDValue CustomDAG::createIDIV(bool IsSigned, EVT ResVT, SDValue Dividend,
                              SDValue Divisor, SDValue Mask,
                              SDValue AVL) const {
  return getNode(IsSigned ? VEISD::VVP_SDIV : VEISD::VVP_UDIV, ResVT,
                 {Dividend, Divisor, Mask, AVL});
}

SDValue CustomDAG::createIREM(bool IsSigned, EVT ResVT, SDValue Dividend,
                              SDValue Divisor, SDValue Mask,
                              SDValue AVL) const {
  // Based on lib/CodeGen/SelectionDAG/TargetLowering.cpp ::expandREM code.
  // X % Y -> X-X/Y*Y
  SDValue Divide = createIDIV(IsSigned, ResVT, Dividend, Divisor, Mask, AVL);
  SDValue Mul = getNode(VEISD::VVP_MUL, ResVT, {Divide, Divisor, Mask, AVL});
  return getNode(VEISD::VVP_SUB, ResVT, {Dividend, Mul, Mask, AVL});
}

static Optional<unsigned> getNonVVPMaskOp(unsigned VVPOC, EVT ResVT) {
  if (!isMaskType(ResVT))
    return None;
  switch (VVPOC) {
  default:
    return None;

  case VEISD::VVP_AND:
    return ISD::AND;
  case VEISD::VVP_OR:
    return ISD::OR;
  case VEISD::VVP_XOR:
    return ISD::XOR;
  }
}
SDValue CustomDAG::getLegalBinaryOpVVP(unsigned VVPOpcode, EVT ResVT, SDValue A,
                                       SDValue B, SDValue Mask, SDValue AVL,
                                       SDNodeFlags Flags) const {
  // Ignore AVL, Mask in mask arithmetic and expand to a standard ISD.
  if (Optional<unsigned> PlainOpc = getNonVVPMaskOp(VVPOpcode, ResVT))
    return getNode(*PlainOpc, ResVT, {A, B});

  // Fold VFRCP.
  if (VVPOpcode == VEISD::VVP_FDIV && Flags.hasAllowReciprocal() &&
      match_FPOne(A))
    return getNode(VEISD::VVP_FRCP, ResVT, {B, Mask, AVL}, Flags);

  // Expand S/UREM.
  if (VVPOpcode == VEISD::VVP_UREM)
    return createIREM(false, ResVT, A, B, Mask, AVL);
  if (VVPOpcode == VEISD::VVP_SREM)
    return createIREM(true, ResVT, A, B, Mask, AVL);

  // Lower to the VVP node by default.
  SDValue V = getNode(VVPOpcode, ResVT, {A, B, Mask, AVL});
  V->setFlags(Flags);
  return V;
}

SDValue CustomDAG::foldAndUnpackMask(SDValue MaskVector, SDValue Mask,
                                     PackElem Part, SDValue AVL) const {
  auto PartV = CreateUnpack(MVT::v256i1, Mask, Part, AVL);
  if (IsAllTrueMask(Mask))
    return PartV;

  auto PartMask = CreateUnpack(MVT::v256i1, Mask, Part, AVL);
  return getNode(ISD::AND, MVT::v256i1, {PartV, PartMask});
}

SDValue CustomDAG::getLegalReductionOpVVP(unsigned VVPOpcode, EVT ResVT,
                                          SDValue VectorV, SDValue Mask,
                                          SDValue AVL,
                                          SDNodeFlags Flags) const {
  if (!isMaskType(VectorV.getValueType())) {
    // Use sequential 'fmul' reduction.
    if (VVPOpcode == VEISD::VVP_REDUCE_FMUL) {
      VVPOpcode = VEISD::VVP_REDUCE_SEQ_FMUL;
      auto FloatOne = DAG.getConstantFP(
          1.0, DL, VectorV.getValueType().getVectorElementType());
      return getNode(VVPOpcode, ResVT, {FloatOne, VectorV, Mask, AVL}, Flags);
    }
    return getNode(VVPOpcode, ResVT, {VectorV, Mask, AVL}, Flags);
  }

  // Mask legalization using vm_popcount
  if (!IsAllTrueMask(Mask)) {
    VectorV = getNode(ISD::AND, MVT::v256i1, {VectorV, Mask});
  }

  auto Pop = CreateMaskPopcount(VectorV, AVL);
  auto LegalPop = DAG.getZExtOrTrunc(Pop, DL, MVT::i32);

  switch (VVPOpcode) {
  default:
    abort(); // TODO implement
  case VEISD::VVP_REDUCE_ADD:
  case VEISD::VVP_REDUCE_XOR: {
    auto OneV = getConstant(1, MVT::i32);
    return getNode(ISD::AND, MVT::i32, {LegalPop, OneV});
  }
  case VEISD::VVP_REDUCE_UMAX:
  case VEISD::VVP_REDUCE_SMIN:
  case VEISD::VVP_REDUCE_OR: {
    // FIXME: Should be 'true' if \p Mask is all-false..
    auto ZeroV = getConstant(0, MVT::i32);
    return getNode(ISD::SETCC, MVT::i32,
                   {LegalPop, ZeroV, DAG.getCondCode(ISD::CondCode::SETNE)});
  }
  case VEISD::VVP_REDUCE_UMIN:
  case VEISD::VVP_REDUCE_SMAX:
  case VEISD::VVP_REDUCE_MUL:
  case VEISD::VVP_REDUCE_AND: {
    return getNode(ISD::SETCC, MVT::i32,
                   {LegalPop, AVL, DAG.getCondCode(ISD::CondCode::SETEQ)});
  }
  }
}

SDValue CustomDAG::getZExtInReg(SDValue Op, EVT VT) const {
  return DAG.getZeroExtendInReg(Op, DL, VT);
}

SDValue CustomDAG::createBitReverse(SDValue ScalarReg) const {
  assert(ScalarReg.getValueType() == MVT::i64);
  return getNode(ISD::BITREVERSE, MVT::i64, ScalarReg);
}

raw_ostream &CustomDAG::print(raw_ostream &Out, SDValue V) const {
  V->print(Out, &DAG);
  return Out;
}

/// } class CustomDAG
} // namespace llvm
