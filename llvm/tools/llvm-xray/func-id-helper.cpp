//===- xray-fc-account.cpp: XRay Function Call Accounting Tool ------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// Implementation of the helper tools dealing with XRay-generated function ids.
//
//===----------------------------------------------------------------------===//

#include "func-id-helper.h"
#include "llvm/Support/Path.h"
#include <sstream>

using namespace llvm;
using namespace xray;

std::string FuncIdConversionHelper::SymbolOrNumber(int32_t FuncId) const {
  auto CacheIt = CachedNames.find(FuncId);
  if (CacheIt != CachedNames.end())
    return CacheIt->second;

  std::ostringstream F;
  auto It = FunctionAddresses.find(FuncId);
  if (It == FunctionAddresses.end()) {
    F << "#" << FuncId;
    return F.str();
  }

  if (auto ResOrErr = Symbolizer.symbolizeCode(BinaryInstrMap, It->second)) {
    auto &DI = *ResOrErr;
    if (DI.FunctionName == "<invalid>")
      F << "@(" << std::hex << It->second << ")";
    else
      F << DI.FunctionName;
  } else
    handleAllErrors(ResOrErr.takeError(), [&](const ErrorInfoBase &) {
      F << "@(" << std::hex << It->second << ")";
    });

  auto S = F.str();
  CachedNames[FuncId] = S;
  return S;
}

std::string FuncIdConversionHelper::FileLineAndColumn(int32_t FuncId) const {
  auto It = FunctionAddresses.find(FuncId);
  if (It == FunctionAddresses.end())
    return "(unknown)";

  std::ostringstream F;
  auto ResOrErr = Symbolizer.symbolizeCode(BinaryInstrMap, It->second);
  if (!ResOrErr) {
    consumeError(ResOrErr.takeError());
    return "(unknown)";
  }

  auto &DI = *ResOrErr;
  F << sys::path::filename(DI.FileName).str() << ":" << DI.Line << ":"
    << DI.Column;

  return F.str();
}
