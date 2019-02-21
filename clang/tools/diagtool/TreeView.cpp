//===- TreeView.cpp - diagtool tool for printing warning flags ------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "DiagTool.h"
#include "DiagnosticNames.h"
#include "clang/Basic/AllDiagnostics.h"
#include "clang/Basic/Diagnostic.h"
#include "clang/Basic/DiagnosticOptions.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/Support/Format.h"
#include "llvm/Support/Process.h"

DEF_DIAGTOOL("tree", "Show warning flags in a tree view", TreeView)

using namespace clang;
using namespace diagtool;

static bool hasColors(const llvm::raw_ostream &out) {
  if (&out != &llvm::errs() && &out != &llvm::outs())
    return false;
  return llvm::errs().is_displayed() && llvm::outs().is_displayed();
}

class TreePrinter {
public:
  llvm::raw_ostream &out;
  const bool ShowColors;
  bool Internal;

  TreePrinter(llvm::raw_ostream &out)
      : out(out), ShowColors(hasColors(out)), Internal(false) {}

  void setColor(llvm::raw_ostream::Colors Color) {
    if (ShowColors)
      out << llvm::sys::Process::OutputColor(Color, false, false);
  }

  void resetColor() {
    if (ShowColors)
      out << llvm::sys::Process::ResetColor();
  }

  static bool isIgnored(unsigned DiagID) {
    // FIXME: This feels like a hack.
    static clang::DiagnosticsEngine Diags(new DiagnosticIDs,
                                          new DiagnosticOptions);
    return Diags.isIgnored(DiagID, SourceLocation());
  }

  static bool enabledByDefault(const GroupRecord &Group) {
    for (const DiagnosticRecord &DR : Group.diagnostics()) {
      if (isIgnored(DR.DiagID))
        return false;
    }

    for (const GroupRecord &GR : Group.subgroups()) {
      if (!enabledByDefault(GR))
        return false;
    }

    return true;
  }

  void printGroup(const GroupRecord &Group, unsigned Indent = 0) {
    out.indent(Indent * 2);

    if (enabledByDefault(Group))
      setColor(llvm::raw_ostream::GREEN);
    else
      setColor(llvm::raw_ostream::YELLOW);

    out << "-W" << Group.getName() << "\n";
    resetColor();

    ++Indent;
    for (const GroupRecord &GR : Group.subgroups()) {
      printGroup(GR, Indent);
    }

    if (Internal) {
      for (const DiagnosticRecord &DR : Group.diagnostics()) {
        if (ShowColors && !isIgnored(DR.DiagID))
          setColor(llvm::raw_ostream::GREEN);
        out.indent(Indent * 2);
        out << DR.getName();
        resetColor();
        out << "\n";
      }
    }
  }

  int showGroup(StringRef RootGroup) {
    ArrayRef<GroupRecord> AllGroups = getDiagnosticGroups();

    if (RootGroup.size() > UINT16_MAX) {
      llvm::errs() << "No such diagnostic group exists\n";
      return 1;
    }

    const GroupRecord *Found =
        std::lower_bound(AllGroups.begin(), AllGroups.end(), RootGroup);

    if (Found == AllGroups.end() || Found->getName() != RootGroup) {
      llvm::errs() << "No such diagnostic group exists\n";
      return 1;
    }

    printGroup(*Found);

    return 0;
  }

  int showAll() {
    ArrayRef<GroupRecord> AllGroups = getDiagnosticGroups();
    llvm::DenseSet<unsigned> NonRootGroupIDs;

    for (const GroupRecord &GR : AllGroups) {
      for (auto SI = GR.subgroup_begin(), SE = GR.subgroup_end(); SI != SE;
           ++SI) {
        NonRootGroupIDs.insert((unsigned)SI.getID());
      }
    }

    assert(NonRootGroupIDs.size() < AllGroups.size());

    for (unsigned i = 0, e = AllGroups.size(); i != e; ++i) {
      if (!NonRootGroupIDs.count(i))
        printGroup(AllGroups[i]);
    }

    return 0;
  }

  void showKey() {
    if (ShowColors) {
      out << '\n';
      setColor(llvm::raw_ostream::GREEN);
      out << "GREEN";
      resetColor();
      out << " = enabled by default\n\n";
    }
  }
};

static void printUsage() {
  llvm::errs() << "Usage: diagtool tree [--internal] [<diagnostic-group>]\n";
}

int TreeView::run(unsigned int argc, char **argv, llvm::raw_ostream &out) {
  // First check our one flag (--flags-only).
  bool Internal = false;
  if (argc > 0) {
    StringRef FirstArg(*argv);
    if (FirstArg.equals("--internal")) {
      Internal = true;
      --argc;
      ++argv;
    }
  }

  bool ShowAll = false;
  StringRef RootGroup;

  switch (argc) {
  case 0:
    ShowAll = true;
    break;
  case 1:
    RootGroup = argv[0];
    if (RootGroup.startswith("-W"))
      RootGroup = RootGroup.substr(2);
    if (RootGroup == "everything")
      ShowAll = true;
    // FIXME: Handle other special warning flags, like -pedantic.
    break;
  default:
    printUsage();
    return -1;
  }

  TreePrinter TP(out);
  TP.Internal = Internal;
  TP.showKey();
  return ShowAll ? TP.showAll() : TP.showGroup(RootGroup);
}
