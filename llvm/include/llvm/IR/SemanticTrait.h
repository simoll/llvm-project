//===-- llvm/Instruction.h - Instruction class definition -------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file defines semantic traits.
// Some intrinsics in LLVM can be described as being a regular operation (such as an fadd) at their core
// with an additional semantic trait. We do this to lift optimizations that are defined in terms of standard IR operations (eg fadd, fmul) to these intrinsics. We keep the existing patterns and rewrite machinery and transparently check the rewrite is consistent with the semantical trait(s) that are attached to the operations.
//
// For example:
//
// @llvm.vp.fadd(<256 x double> %a, <256 x double> %b,
//               <256 x i1> %m. i32 %avl)
//
//   This is a vector-predicated fadd instruction with a %mask and %evl parameter
//   (https://llvm.org/docs/LangRef.html#vector-predication-intrinsics).
//   However, at its core it is just an 'fadd'. 
//
//   Consider the fma-fusion rewrite pattern (fadd (fmul x,y) z) --> (fma x, y, z).
//   If the 'fadd' is actually an 'llvm.vp.fadd" and the 'fmul' is actually an
//   'llvm.vp.fmul', we can perform the rewrite using the %mask and %evl of the
//   'fadd' node.
// 
//
// @llvm.experimental.constrained.fadd(double %a, double %b,
//                                     metadata <rounding mode> metadata,
//                                     <exception behavior>)
//
//   This is an fadd with a possibly non-default rounding mode and exception behavior.
//   (https://llvm.org/docs/LangRef.html#constrained-floating-point-intrinsics).
//   In this case, the operation matches the semantics of a regular 'fadd'
//   exactly, if the rounding mode is 'round.tonearest' and the exception
//   behavior is 'fpexcept.ignore'.
//   Re-considering the case of fma fusion, this time with two constrained fp
//   intrinsics.  If the rounding mode is tonearest for either and the
//   'llvm.experimental.contrained.fmul' does not throw, we are good to apply
//   the rewrite and emit a contrained fma with the exception flad of the
//   'fadd'.
// 
// There is also a proposal to add complex arithmetic intrinsics to LLVM. In
// that case, the operation is semantically an 'fadd', if we consider the space
// of complex floating-point numbers and their operations.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_IR_SEMANTICTRAIT_H
#define LLVM_IR_SEMANTICTRAIT_H

#include <llvm/IR/Value.h>
#include <llvm/IR/Instructions.h>

namespace llvm {

/// Trait-augmented Types {
/// Your trait is a first-class property within these trait extended classes.

template<typename SemaTrait>
struct ExtInstruction {
  // TODO When implementing a new Trait, template-specialize this class for
  // your Trait type and implement all functions from llvm::Instruction here,
  // pretending that your intrinsic actually was that instruction.
};

template<typename SemaTrait>
struct ExtBinaryOperator {
  // TODO When implementing a new Trait, template-specialize this class for
  // your Trait type and implement all functions from llvm::BinaryOperator here,
  // pretending that your intrinsic actually was that instruction.
};

// The trait context serves two purposes:
// 1. It is used in pattern matching to check that all instructions in the
//    pattern are trait-compatible.
// 2. To transfer all trait-info to the TraitBuilder<Trait> necessary to emit
//    trait-compatible instructions. That is, the TraitContext<Trait> initialized
//    by a given ExtInstruction<Trait> is sufficient for the TraitBuilder<Trait> to
//    generate instructions that have the same trait as the initializing object.
template<typename Trait>
struct TraitContext {};

// The trait builder is a specialized IRBuilder that emits trait-compatible
// instructions.
template<typename Trait>
struct TraitBuilder {};

/// } Trait-augmented Types {

/// Trait casting {
/// These cast operators are instantiated in terms of actual IR class types, such as 'Instruction' or 'BinaryOperator'.
/// However, different to a normal llvm::cast we are really casting into the trait-extended type hierarchy. That is
///
/// trait_cast<Trait, Instruction>(V) actually casts \p V to ExtInstruction<Trait>.
template<typename Trait, typename ValueDerivedType>
struct TraitCastHelper {
};

// trait_cast impl
template <typename Trait, typename ValueDerivedType>
static typename TraitCastHelper<Trait, ValueDerivedType>::TraitExtendedType&
trait_cast(Value &V) {
  using TraitExtendedType =
      typename TraitCastHelper<Trait, ValueDerivedType>::TraitExtendedType;
  return cast<TraitExtendedType>(V);
}

// trait_isa impl
template <typename Trait, typename ValueDerivedType>
static typename TraitCastHelper<Trait, ValueDerivedType>::TraitExtendedType&
trait_isa(Value &V) {
  using TraitExtendedType =
      typename TraitCastHelper<Trait, ValueDerivedType>::TraitExtendedType;
  return isa<TraitExtendedType>(V);
}

// ExtInstruction cast
template<typename Trait>
struct TraitCastHelper<Trait, Instruction> {
  using TraitExtendedType = ExtInstruction<Trait>;
};

// ExtBinaryOperator cast
template<typename Trait>
struct TraitCastHelper<Trait, BinaryOperator> {
  using TraitExtendedType = ExtBinaryOperator<Trait>;
};
/// } Trait casting

} // end namespace llvm

#endif // LLVM_IR_INSTRUCTION_H
