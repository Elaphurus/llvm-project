#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/AST/StmtVisitor.h"
#include "clang/Analysis/Analyses/Dominators.h"
#include "clang/Analysis/Analyses/LiveVariables.h"
#include "clang/StaticAnalyzer/Checkers/BuiltinCheckerRegistration.h"
#include "clang/StaticAnalyzer/Core/BugReporter/BugType.h"
#include "clang/StaticAnalyzer/Core/Checker.h"
#include "clang/StaticAnalyzer/Core/CheckerManager.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/CallDescription.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/CallEvent.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/CheckerContext.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/ExprEngine.h"
#include "clang/Tooling/Tooling.h"
#include "llvm/ADT/StringSwitch.h"
#include "llvm/Support/Process.h"
#include <utility>

using namespace clang;
using namespace ento;
using namespace tooling;

#define dbp llvm::outs()

namespace {

struct PyMethodDef {
  const StringLiteral *ml_name;
  const FunctionDecl *ml_meth;
  const IntegerLiteral *ml_flags;
  const StringRef ml_doc;

  PyMethodDef() : ml_name(NULL), ml_meth(NULL), ml_flags(NULL), ml_doc(NULL) {}
};

typedef std::vector<PyMethodDef> PyMethVec;

static std::vector<const FunctionDecl *> getPyMethFDs(PyMethVec PyMeths) {
  std::vector<const FunctionDecl *> PyMethFDs;
  for (auto I = PyMeths.begin(); I != PyMeths.end(); ++I) {
    PyMethodDef pymeth = *I;
    const FunctionDecl *ml_meth = pymeth.ml_meth;
    PyMethFDs.push_back(ml_meth);
  }
  return PyMethFDs;
}

static void dbpPyMethodDef(PyMethodDef p, BugReporter &BR) {
  dbp << p.ml_name->getString() << ", ";

  const SourceManager &SM = BR.getSourceManager();
  SourceLocation Loc = SM.getSpellingLoc(p.ml_meth->getLocation());
  dbp << p.ml_meth->getNameAsString() << "@" << Loc.printToString(SM) << ", ";

  dbp << p.ml_flags->getValue().getZExtValue() << ", ";

  dbp << p.ml_doc << "\n";
}

class PyCMethodFinder : public Checker<check::ASTDecl<TranslationUnitDecl>> {
private:
  mutable const TranslationUnitDecl *Tud;
  AnalysisManager &Mgr;
  BugReporter &BR;

public:
  PyCMethodFinder(const TranslationUnitDecl *TudArg, AnalysisManager &MgrArg,
                  BugReporter &BRArg)
      : Tud(TudArg), Mgr(MgrArg), BR(BRArg) {}

  mutable PyMethVec PyMeths;

  void checkASTDecl(const TranslationUnitDecl *TudArg, AnalysisManager &MgrArg,
                    BugReporter &BRArg) const {
    struct LocalVisitor : public RecursiveASTVisitor<LocalVisitor> {
      const PyCMethodFinder *Checker;
      bool shouldVisitTemplateInstantiations() const { return true; }
      bool shouldVisitImplicitCode() const { return true; }
      explicit LocalVisitor(const PyCMethodFinder *Checker)
          : Checker(Checker) {}

      bool VisitVarDecl(const VarDecl *VD) {
        Checker->visitVariable(VD);
        return true;
      }
    };
    LocalVisitor visitor(this);
    visitor.TraverseDecl(const_cast<TranslationUnitDecl *>(Tud));
  }

  bool isPyMethodDef(RecordDecl *RD) const {
    IdentifierInfo *RDInfo = RD->getIdentifier();
    if (!RDInfo) {
      return false;
    }
    if (RDInfo->isStr("PyMethodDef")) {
      return true;
    }
    return false;
  }

  const Stmt *VisitChild(const Stmt *S) const {
    if (const CastExpr *E = dyn_cast<CastExpr>(S)) {
      return VisitChild(E->getSubExpr());
    }
    if (const ParenExpr *E = dyn_cast<ParenExpr>(S)) {
      return VisitChild(E->getSubExpr());
    }
    return S;
  }

  PyMethodDef VisitPyMethodDef(const Stmt *S) const {
    PyMethodDef pymeth = PyMethodDef();

    Stmt::const_child_iterator I = S->children().begin();

    const Stmt *ml_name_stmt = VisitChild(*I);
    if (const IntegerLiteral *IL = dyn_cast<IntegerLiteral>(ml_name_stmt)) {
      return pymeth;
    }
    if (const StringLiteral *SL = dyn_cast<StringLiteral>(ml_name_stmt)) {
      pymeth.ml_name = SL;
    }

    const Stmt *ml_meth_stmt = VisitChild(*++I);
    if (const DeclRefExpr *RE = dyn_cast<DeclRefExpr>(ml_meth_stmt)) {
      const ValueDecl *VD = RE->getDecl();
      if (const FunctionDecl *FD = dyn_cast<FunctionDecl>(VD)) {
        pymeth.ml_meth = FD;
      }
    }

    const Stmt *ml_flags_stmt = VisitChild(*++I);
    if (const IntegerLiteral *IL = dyn_cast<IntegerLiteral>(ml_flags_stmt)) {
      pymeth.ml_flags = IL;
    }

    const Stmt *ml_doc_stmt = VisitChild(*++I);
    if (const StringLiteral *SL = dyn_cast<StringLiteral>(ml_doc_stmt)) {
      pymeth.ml_doc = SL->getString();
    }
    if (const DeclRefExpr *RE = dyn_cast<DeclRefExpr>(ml_doc_stmt)) {
      const ValueDecl *VD = RE->getDecl();
      pymeth.ml_doc = VD->getNameAsString();
    }

    return pymeth;
  }

  void visitVariable(const VarDecl *VD) const {
    const ArrayType *ArrTy = VD->getType()->getAsArrayTypeUnsafe();
    if (ArrTy == nullptr) {
      return;
    }
    uint64_t Elts = 0;
    if (const ConstantArrayType *CArrTy = dyn_cast<ConstantArrayType>(ArrTy)) {
      Elts = CArrTy->getSize().getZExtValue();
    }
    if (Elts == 0) {
      return;
    }
    const RecordType *RT = ArrTy->getElementType()->getAs<RecordType>();
    if (RT == nullptr) {
      return;
    }

    RecordDecl *RD = RT->getDecl();
    if (isPyMethodDef(RD)) {
      const SourceManager &SM = BR.getSourceManager();
      SourceLocation Loc = VD->getLocation();
      dbp << VD->getNameAsString() << "@" << Loc.printToString(SM) << "\n";
      // VD->getDefinition()->dump();

      if (const Expr *InitExpr = VD->getInit()) {
        for (const Stmt *Child : InitExpr->children()) {
          if (Child) {
            // Child->dump();
            PyMethodDef pymeth = VisitPyMethodDef(Child);
            if (pymeth.ml_name) {
              // dbpPyMethodDef(pymeth, BR);
              PyMeths.push_back(pymeth);
            }
          }
        }
      }
    }
  }
};

static PyMethVec FindPyCMethod(const TranslationUnitDecl *Tud,
                               AnalysisManager &Mgr, BugReporter &BR) {
  PyCMethodFinder Finder(Tud, Mgr, BR);
  Finder.checkASTDecl(Tud, Mgr, BR);
  return Finder.PyMeths;
}

struct ExnState {
private:
  enum Kind { Exn, NoExn } K;
  ExnState(Kind InK) : K(InK) {}

public:
  bool hasExn() const { return K == Exn; }
  bool hasNoExn() const { return K == NoExn; }

  static ExnState getExn() { return ExnState(Exn); }
  static ExnState getNoExn() { return ExnState(NoExn); }

  bool operator==(const ExnState &X) const { return K == X.K; }
  void Profile(llvm::FoldingSetNodeID &ID) const { ID.AddInteger(K); }
};

class PyCExnChecker
    : public Checker<check::ASTDecl<TranslationUnitDecl>, check::ASTCodeBody,
                     check::PostCall, check::PreStmt<ReturnStmt>> {
private:
  mutable PyMethVec PyMeths;

  std::set<std::string> RaiseFNs, ClearFNs, CleanupFNs, ImplicitRaiseFNs;
  std::unique_ptr<BugType> UncaughtExnBugType;

  void reportUncaughtExn(const ReturnStmt *RS, CheckerContext &C) const;

  void reportResultWhenExn(const ReturnStmt *RS, CheckerContext &C) const;

  void reportUnexpectedControlFlow(const FunctionDecl *FD,
                                   CheckerContext &C) const;

public:
  PyCExnChecker();

  // Find Python's C foreign function declarations.
  void checkASTDecl(const TranslationUnitDecl *Tud, AnalysisManager &Mgr,
                    BugReporter &BR) const;

  // TODO: AST-based checkers
  void checkASTCodeBody(const Decl *D, AnalysisManager &Mgr,
                        BugReporter &BR) const;

  // Process exception handling Python/C APIs.
  void checkPostCall(const CallEvent &Call, CheckerContext &C) const;
  // Process return statements.
  void checkPreStmt(const ReturnStmt *RS, CheckerContext &C) const;
};

} // namespace

REGISTER_MAP_WITH_PROGRAMSTATE(ExnMap, const FunctionDecl *, ExnState)

PyCExnChecker::PyCExnChecker()
    : RaiseFNs({"PyErr_SetString", "PyErr_SetObject"}),
      ClearFNs({"PyErr_Clear"}), CleanupFNs({"Py_DECREF"}),
      ImplicitRaiseFNs({"PyArg_ParseTuple"}) {
  UncaughtExnBugType.reset(
      new BugType(this, "Uncaught Exception", "Python/C Exception Error"));
}

void PyCExnChecker::checkASTDecl(const TranslationUnitDecl *Tud,
                                 AnalysisManager &Mgr, BugReporter &BR) const {
  PyMeths = FindPyCMethod(Tud, Mgr, BR);
  for (auto I = PyMeths.begin(); I != PyMeths.end(); ++I) {
    PyMethodDef pymeth = *I;
    dbpPyMethodDef(pymeth, BR);
    // TODO: Initialize foreign function's ExnState with NoExn.
  }
}

void PyCExnChecker::checkASTCodeBody(const Decl *D, AnalysisManager &Mgr,
                                     BugReporter &BR) const {
  /*
  std::vector<const FunctionDecl *> PyMethFDs = getPyMethFDs(PyMeths);
  if (const FunctionDecl *FD = dyn_cast<FunctionDecl>(D)) {
    if (std::find(PyMethFDs.begin(), PyMethFDs.end(), FD) != PyMethFDs.end()) {
      if (IdentifierInfo *II = FD->getIdentifier()) {
        dbp << II->getName() << "\n";
      }
    }
  }
  */
}

void PyCExnChecker::checkPostCall(const CallEvent &Call,
                                  CheckerContext &C) const {
  // Get the called Python/C API.
  if (const FunctionDecl *FD = dyn_cast<FunctionDecl>(Call.getDecl())) {
    if (IdentifierInfo *II = FD->getIdentifier()) {
      dbp << II->getName() << "\n";
      // Get the function that calls the Python/C API.
      const StackFrameContext *SFC = C.getStackFrame();
      const FunctionDecl *CallerFD = SFC->getDecl()->getAsFunction();

      ProgramStateRef State = C.getState();
      const ExnState *ES = State->get<ExnMap>(CallerFD);
      if (RaiseFNs.find(II->getName().str()) != RaiseFNs.end()) {
        dbp << "raise exn\n";
        State = State->set<ExnMap>(CallerFD, ExnState::getExn());
      } else if (ImplicitRaiseFNs.find(II->getName().str()) !=
                 ImplicitRaiseFNs.end()) {
        if (ES && ES->hasExn()) {
          reportUnexpectedControlFlow(FD, C);
        }
        dbp << "implicitly raise exn\n";
        State = State->set<ExnMap>(CallerFD, ExnState::getExn());
      } else if (ClearFNs.find(II->getName().str()) != ClearFNs.end()) {
        dbp << "clear exn\n";
        State = State->set<ExnMap>(CallerFD, ExnState::getNoExn());
      } else if (CleanupFNs.find(II->getName().str()) == CleanupFNs.end()) {
        // not one of RaiseFNs, ImplicitRaiseFNs, ClearFNs and CleanupFNs
        if (ES && ES->hasExn()) {
          reportUnexpectedControlFlow(FD, C);
        }
      }
      C.addTransition(State);
    }
  }
}

void PyCExnChecker::checkPreStmt(const ReturnStmt *RS,
                                 CheckerContext &C) const {
  const Expr *E = RS->getRetValue();
  if (!E) {
    return;
  }
  SVal RetV = C.getSVal(E);
  const StackFrameContext *SFC = C.getStackFrame();
  const FunctionDecl *FD = SFC->getDecl()->getAsFunction();
  ProgramStateRef State = C.getState();
  const ExnState *ES = State->get<ExnMap>(FD);
  if (RetV.isZeroConstant()) {
    dbp << "return null in " << FD->getIdentifier()->getName() << "\n";
    if (!ES) {
      // Return NULL when exception state is Unknown.
      // TODO: Modify after initializing foreign function's ExnState with NoExn.
      reportUncaughtExn(RS, C);
      return;
    }
    if (ES->hasNoExn()) {
      // Return NULL when exception state is NoExn.
      reportUncaughtExn(RS, C);
      return;
    }
  } else {
    if (ES && ES->hasExn()) {
      // Return non-NULL result when exception state is Exn.
      reportResultWhenExn(RS, C);
      return;
    }
  }
  C.addTransition(State);
}

void PyCExnChecker::reportUncaughtExn(const ReturnStmt *RS,
                                      CheckerContext &C) const {
  ExplodedNode *ErrNode = C.generateErrorNode();
  if (!ErrNode) {
    return;
  }
  auto R = std::make_unique<PathSensitiveBugReport>(
      *UncaughtExnBugType, "Returning NULL without setting an exception",
      ErrNode);
  R->addRange(RS->getSourceRange());
  C.emitReport(std::move(R));
}

void PyCExnChecker::reportResultWhenExn(const ReturnStmt *RS,
                                        CheckerContext &C) const {
  ExplodedNode *ErrNode = C.generateErrorNode();
  if (!ErrNode) {
    return;
  }
  auto R = std::make_unique<PathSensitiveBugReport>(
      *UncaughtExnBugType, "Returning a result with an exception set", ErrNode);
  R->addRange(RS->getSourceRange());
  C.emitReport(std::move(R));
}

void PyCExnChecker::reportUnexpectedControlFlow(const FunctionDecl *FD,
                                                CheckerContext &C) const {
  ExplodedNode *ErrNode = C.generateErrorNode();
  if (!ErrNode) {
    return;
  }
  auto R = std::make_unique<PathSensitiveBugReport>(
      *UncaughtExnBugType,
      "Unexpected control flow between raising exception and returning",
      ErrNode);
  R->addRange(FD->getSourceRange());
  C.emitReport(std::move(R));
}

void ento::registerPyCExnChecker(CheckerManager &Mgr) {
  Mgr.registerChecker<PyCExnChecker>();
}

bool ento::shouldRegisterPyCExnChecker(const CheckerManager &Mgr) {
  return true;
}
