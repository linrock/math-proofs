#!/usr/bin/env python3
"""CI package selection, manifest validation, environment comparison, and summary generator."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import pathlib
import re
import resource
import shutil
import subprocess
import sys
import tempfile
import time
import tomllib
import urllib.request
from typing import Any

REPO_ROOT = pathlib.Path(__file__).resolve().parents[2]
EXPECTED_TOOLCHAIN = "leanprover/lean4:v4.35.0-rc2"
EXPECTED_MATHLIB_REV = "065356127b1dc0016f66b7283ce0ce2c4055aa55"
PERMITTED_AXIOMS = ["propext", "Classical.choice", "Quot.sound"]
VALID_SOURCE_RELS = {"formalizes", "adapts", "independently-proves"}

SKIP_DIRS = {".git", ".lake", ".verification", "verification", "verification-local", "fc-shared-lib"}
FORBIDDEN_SUFFIXES = (".swp", ".swo", ".swn", "~", ".olean", ".ilean", ".ir", ".trace")
DOC_ONLY_FILENAMES = {
    "README.md",
    "BUILD.md",
    "THIRD_PARTY.md",
    "LICENSE",
    ".gitignore",
    "formalization.yaml",
}

ENV_COMPARE_LEAN = """module

import Lean
open Lean

structure CoreAuditRow where
  name : String
  kind : String
  declaration : String
deriving ToJson

def moduleOfConst (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some idx => env.header.moduleNames.getD idx.toNat Name.anonymous
  | none => Name.anonymous

partial def collectChallengeDefs (env : Environment) (work : List Name) (seen : NameSet) (acc : Array (String × Name)) : NameSet × Array (String × Name) :=
  match work with
  | [] => (seen, acc)
  | n :: rest =>
    if seen.contains n then
      collectChallengeDefs env rest seen acc
    else
      let seen := seen.insert n
      match env.find? n with
      | none => collectChallengeDefs env rest seen acc
      | some info =>
        let isChal := moduleOfConst env n == `Challenge && !n.isInternalDetail
        if isChal then
          match info with
          | .defnInfo v =>
            collectChallengeDefs env (v.value.getUsedConstants.toList ++ info.type.getUsedConstants.toList ++ rest) seen (acc.push ("def", n))
          | .inductInfo i =>
            collectChallengeDefs env (i.ctors ++ info.type.getUsedConstants.toList ++ rest) seen (acc.push ("inductive", n))
          | .ctorInfo c =>
            collectChallengeDefs env (c.induct :: info.type.getUsedConstants.toList ++ rest) seen (acc.push ("ctor", n))
          | _ =>
            collectChallengeDefs env (info.type.getUsedConstants.toList ++ rest) seen acc
        else
          collectChallengeDefs env rest seen acc

private partial def addTypeProxy
    (rawEnv : Environment) (name : Name) : StateT (Environment × NameSet) IO Unit := do
  let (env, seen) ← get
  if env.contains name || seen.contains name then
    return
  let some dependency := rawEnv.find? name
    | throw <| IO.userError s!"audit declaration depends on missing constant {name}"
  set (env, seen.insert name)
  for used in dependency.type.getUsedConstants do
    addTypeProxy rawEnv used
  if moduleOfConst rawEnv name == `Challenge then
    match dependency with
    | .defnInfo v =>
      for used in v.value.getUsedConstants do
        addTypeProxy rawEnv used
    | .inductInfo i =>
      for c in i.ctors do
        addTypeProxy rawEnv c
    | .ctorInfo c =>
      addTypeProxy rawEnv c.induct
    | _ => pure ()
  let (env, seen) ← get
  let proxy : Declaration := .axiomDecl {
    name := dependency.name
    levelParams := dependency.levelParams
    type := dependency.type
    isUnsafe := false
  }
  let ctx : Core.Context := {
    fileName := "<palomar-core-notation-audit-proxy>"
    fileMap := default
    options := ({} : Options).setBool `debug.skipKernelTC true
  }
  let (_, state) ← (Lean.addDecl proxy).toIO ctx { env }
  set (state.env, seen)

private def printCoreDecl (rawEnv trustedEnv : Environment) (kind : String) (name : Name) : IO String := do
  let opts := ({} : Options)
    |>.set `pp.notation false
    |>.set `pp.fullNames true
    |>.set `pp.fieldNotation false
    |>.set `pp.proofs true
    |>.set `pp.deepTerms true
    |>.set `pp.maxSteps 1000000
  let ctx : Core.Context := {
    fileName := "<palomar-core-notation-audit>"
    fileMap := default
    options := opts
  }
  let state : Core.State := { env := trustedEnv }
  let (sig, _) ← (PrettyPrinter.ppSignature name).run' {} |>.toIO ctx state
  if kind == "def" then
    if let some (.defnInfo v) := rawEnv.find? name then
      let (valFmt, _) ← (PrettyPrinter.ppExpr v.value).run' {} |>.toIO ctx state
      return s!"def {sig.fmt.pretty} :=\\n  {valFmt.pretty}"
  return s!"{kind} {sig.fmt.pretty}"

def isSameUpstreamModule (envC envS : Environment) (nC nS : Name) : Bool :=
  let mC := moduleOfConst envC nC
  let mS := moduleOfConst envS nS
  nC == nS && mC != Name.anonymous && mC != `Challenge && mC == mS

def levelsEquiv (us vs : List Level) : Bool :=
  us.length == vs.length && (us.zip vs).all fun (u, v) => Level.isEquiv u v

def pushUnvisited (verified : NameSet) (arr : Array Name) (work : List Name) : List Name :=
  arr.foldl (fun acc c => if verified.contains c then acc else c :: acc) work

def isInternalProofApp (envC envS : Environment) (eC eS : Expr) : Option (Name × Name) :=
  match eC.getAppFn, eS.getAppFn with
  | .const n1 _, .const n2 _ =>
    if n1.isInternalDetail && n2.isInternalDetail then
      match envC.find? n1, envS.find? n2 with
      | some (.thmInfo _), some (.thmInfo _) => some (n1, n2)
      | _, _ => none
    else
      none
  | _, _ => none

mutual
partial def checkConstPair (envC envS : Environment) (visited : Std.HashSet (Name × Name)) (nC nS : Name) : IO (Std.HashSet (Name × Name)) := do
  if visited.contains (nC, nS) then
    return visited
  if isSameUpstreamModule envC envS nC nS then
    return visited.insert (nC, nS)
  if (!nC.isInternalDetail || !nS.isInternalDetail) && nC != nS then
    throw <| IO.userError s!"Public constant name mismatch: Challenge has {nC}, Solution has {nS}"
  let visited := visited.insert (nC, nS)
  let some infoC := envC.find? nC
    | throw <| IO.userError s!"Constant {nC} missing in Challenge"
  let some infoS := envS.find? nS
    | throw <| IO.userError s!"Constant {nS} missing in Solution"
  if infoC.levelParams.length != infoS.levelParams.length then
    throw <| IO.userError s!"Level params length mismatch on {nC} vs {nS}"
  let ls := infoC.levelParams.map Level.param
  if nC.isInternalDetail && nS.isInternalDetail then
    if infoC matches .thmInfo _ && infoS matches .thmInfo _ then
      return visited
  let visited ← checkExprEq envC envS visited infoC.type (infoS.instantiateTypeLevelParams ls)
  match infoC, infoS with
  | .thmInfo _, .thmInfo _ =>
    return visited
  | .defnInfo vC, .defnInfo vS =>
    if vC.safety != .safe || vS.safety != .safe then
      throw <| IO.userError s!"Unsafe/partial definition {nC} / {nS}"
    checkExprEq envC envS visited vC.value (infoS.instantiateValueLevelParams! ls)
  | .inductInfo iC, .inductInfo iS =>
    if iC.numParams != iS.numParams || iC.numIndices != iS.numIndices || iC.ctors.length != iS.ctors.length then
      throw <| IO.userError s!"Inductive/structure mismatch on {nC}"
    let mut vis := visited
    for (c1, c2) in iC.ctors.zip iS.ctors do
      vis ← checkConstPair envC envS vis c1 c2
    return vis
  | .ctorInfo cC, .ctorInfo cS =>
    if cC.induct != cS.induct || cC.cidx != cS.cidx || cC.numParams != cS.numParams || cC.numFields != cS.numFields then
      throw <| IO.userError s!"Constructor mismatch on {nC}"
    checkConstPair envC envS visited cC.induct cS.induct
  | .recInfo rC, .recInfo rS =>
    if rC.numParams != rS.numParams || rC.numIndices != rS.numIndices || rC.numMotives != rS.numMotives || rC.numMinors != rS.numMinors || rC.rules.length != rS.rules.length || rC.k != rS.k || rC.all.length != rS.all.length then
      throw <| IO.userError s!"Recursor mismatch on {nC}"
    let mut vis := visited
    for (ind1, ind2) in rC.all.zip rS.all do
      vis ← checkConstPair envC envS vis ind1 ind2
    return vis
  | .axiomInfo _, _ | _, .axiomInfo _ =>
    throw <| IO.userError s!"Statement definition {nC} / {nS} is an axiom"
  | .opaqueInfo _, _ | _, .opaqueInfo _ =>
    throw <| IO.userError s!"Statement definition {nC} / {nS} is opaque"
  | _, _ =>
    throw <| IO.userError s!"Constant kind mismatch between {nC} and {nS}"

partial def checkExprEq (envC envS : Environment) (visited : Std.HashSet (Name × Name)) (eC eS : Expr) : IO (Std.HashSet (Name × Name)) := do
  match eC, eS with
  | .mdata _ eC', _ => checkExprEq envC envS visited eC' eS
  | _, .mdata _ eS' => checkExprEq envC envS visited eC eS'
  | .bvar i, .bvar j =>
    if i != j then throw <| IO.userError s!"Bound variable mismatch: {i} vs {j}"
    return visited
  | .sort u, .sort v =>
    if !Level.isEquiv u v then throw <| IO.userError s!"Sort level mismatch: {u} vs {v}"
    return visited
  | .lit l1, .lit l2 =>
    if l1 != l2 then throw <| IO.userError s!"Literal mismatch"
    return visited
  | .const n1 us1, .const n2 us2 =>
    if !levelsEquiv us1 us2 then throw <| IO.userError s!"Universe levels mismatch on {n1} vs {n2}"
    checkConstPair envC envS visited n1 n2
  | .app f1 a1, .app f2 a2 =>
    if let some (n1, n2) := isInternalProofApp envC envS eC eS then
      checkConstPair envC envS visited n1 n2
    else
      let visited ← checkExprEq envC envS visited f1 f2
      checkExprEq envC envS visited a1 a2
  | .lam _ d1 b1 _, .lam _ d2 b2 _ =>
    let visited ← checkExprEq envC envS visited d1 d2
    checkExprEq envC envS visited b1 b2
  | .forallE _ d1 b1 _, .forallE _ d2 b2 _ =>
    let visited ← checkExprEq envC envS visited d1 d2
    checkExprEq envC envS visited b1 b2
  | .letE _ t1 v1 b1 _, .letE _ t2 v2 b2 _ =>
    let visited ← checkExprEq envC envS visited t1 t2
    let visited ← checkExprEq envC envS visited v1 v2
    checkExprEq envC envS visited b1 b2
  | .proj t1 i1 s1, .proj t2 i2 s2 =>
    if i1 != i2 then throw <| IO.userError s!"Projection index mismatch on {t1} vs {t2}"
    let visited ← checkConstPair envC envS visited t1 t2
    checkExprEq envC envS visited s1 s2
  | _, _ =>
    throw <| IO.userError s!"Expression structure mismatch:\n  Challenge: {eC}\n  Solution:  {eS}"
end

partial def verifyProofCone (env : Environment) (verified : NameSet) (worklist : List Name) : IO NameSet := do
  match worklist with
  | [] => pure verified
  | n :: rest =>
    if verified.contains n then
      verifyProofCone env verified rest
    else
      let verified := verified.insert n
      let some info := env.find? n
        | throw <| IO.userError s!"Constant {n} missing in Solution environment"
      if info.isUnsafe then
        throw <| IO.userError s!"Unsafe constant {n} in Solution proof cone"
      let mut nextWork := pushUnvisited verified info.type.getUsedConstants rest
      match info with
      | .axiomInfo _ =>
        let s := n.toString
        if s != "propext" && s != "Classical.choice" && s != "Quot.sound" then
          throw <| IO.userError s!"Disallowed axiom {s} in Solution proof cone"
      | .defnInfo v =>
        if v.safety != .safe then
          throw <| IO.userError s!"Unsafe/partial definition {n} in Solution proof cone"
        nextWork := pushUnvisited verified v.value.getUsedConstants nextWork
      | .opaqueInfo v =>
        if (env.find? (n ++ `_unsafe_rec)).isSome then
          throw <| IO.userError s!"Partial definition {n} in Solution proof cone"
        nextWork := pushUnvisited verified v.value.getUsedConstants nextWork
      | .inductInfo i =>
        for c in i.all ++ i.ctors do
          if !verified.contains c then nextWork := c :: nextWork
      | .ctorInfo c =>
        if !verified.contains c.induct then nextWork := c.induct :: nextWork
      | .recInfo r =>
        for c in r.all do
          if !verified.contains c then nextWork := c :: nextWork
        for rule in r.rules do
          nextWork := pushUnvisited verified rule.rhs.getUsedConstants nextWork
      | .thmInfo v =>
        nextWork := pushUnvisited verified v.value.getUsedConstants nextWork
      | .quotInfo _ =>
        pure ()
      verifyProofCone env verified nextWork

public unsafe def main (args : List String) : IO UInt32 := do
  let sysroot ← findSysroot
  initSearchPath sysroot [System.FilePath.mk ".lake/build/lib/lean"]
  let rawC ← importModules (loadExts := false) #[{ module := `Challenge, importAll := true }] {} 0
  let rawS ← importModules (loadExts := false) #[{ module := `Solution, importAll := true }] {} 0
  let envC := rawC.setExporting false
  let envS := rawS.setExporting false
  if envS.allImportedModuleNames.contains `Challenge then
    throw <| IO.userError "Solution must not import Challenge"
  let defArgs := (args.filter (·.startsWith "--def:")).map (fun s => (s.drop 6).toString)
  let thmArgs := args.filter (fun s => !s.startsWith "--def:")
  let targetThms : NameSet := thmArgs.foldl (fun acc raw => acc.insert raw.toName) {}
  if let some idx := envC.header.moduleNames.idxOf? `Challenge then
    let modC := envC.header.moduleData[idx]!
    for imp in modC.imports do
      let root := imp.module.getRoot
      if root != `Mathlib && root != `Init then
        throw <| IO.userError s!"Challenge.lean imports non-Mathlib module {imp.module}"
    for ci in modC.constants do
      if ci.isUnsafe then
        throw <| IO.userError s!"Unsafe declaration {ci.name} in Challenge.lean"
      if ci.type.getUsedConstants.contains `sorryAx then
        throw <| IO.userError s!"Type of {ci.name} in Challenge.lean contains sorry"
      if ci.type.getUsedConstants.any targetThms.contains then
        throw <| IO.userError s!"Type of {ci.name} in Challenge.lean depends on a target theorem"
      match ci with
      | .axiomInfo _ =>
        throw <| IO.userError s!"Custom axiom {ci.name} in Challenge.lean"
      | .opaqueInfo _ =>
        throw <| IO.userError s!"Opaque declaration {ci.name} in Challenge.lean"
      | .defnInfo v =>
        if v.safety != .safe then
          throw <| IO.userError s!"Unsafe/partial definition {ci.name} in Challenge.lean"
        if v.value.getUsedConstants.contains `sorryAx then
          throw <| IO.userError s!"Definition {ci.name} in Challenge.lean contains sorry"
        if v.value.getUsedConstants.any targetThms.contains then
          throw <| IO.userError s!"Definition {ci.name} in Challenge.lean depends on a target theorem"
      | .thmInfo v =>
        if !targetThms.contains ci.name then
          if v.value.getUsedConstants.contains `sorryAx then
            throw <| IO.userError s!"Non-target theorem or proof obligation {ci.name} in Challenge.lean contains sorry"
          if v.value.getUsedConstants.any targetThms.contains then
            throw <| IO.userError s!"Non-target theorem or proof obligation {ci.name} in Challenge.lean depends on a target theorem"
      | _ => pure ()
  let mut visited : Std.HashSet (Name × Name) := {}
  let mut verifiedCone : NameSet := {}
  for rawDef in defArgs do
    let dName := rawDef.toName
    let some infoC := envC.find? dName
      | throw <| IO.userError s!"Definition {dName} missing in Challenge"
    let some infoS := envS.find? dName
      | throw <| IO.userError s!"Definition {dName} missing in Solution"
    if moduleOfConst envC dName != `Challenge then
      throw <| IO.userError s!"Definition {dName} is not declared in Challenge.lean"
    match infoC, infoS with
    | .defnInfo _, .defnInfo _ | .inductInfo _, .inductInfo _ => pure ()
    | _, _ => throw <| IO.userError s!"{dName} must be a definition or inductive type in both Challenge and Solution"
    visited ← checkConstPair envC envS visited dName dName
    verifiedCone ← verifyProofCone envS verifiedCone [dName]
    IO.println s!"DEF_MATCH {rawDef}"
  for raw in thmArgs do
    let thm := raw.toName
    let some infoC := envC.find? thm
      | throw <| IO.userError s!"Theorem {thm} missing in Challenge"
    let some infoS := envS.find? thm
      | throw <| IO.userError s!"Theorem {thm} missing in Solution"
    if moduleOfConst envC thm != `Challenge then
      throw <| IO.userError s!"Theorem {thm} is not declared in Challenge.lean"
    match infoC, infoS with
    | .thmInfo _, .thmInfo _ => pure ()
    | _, _ => throw <| IO.userError s!"{thm} must be a theorem in both Challenge and Solution"
    visited ← checkConstPair envC envS visited thm thm
    verifiedCone ← verifyProofCone envS verifiedCone [thm]
    IO.println s!"ENV_MATCH {raw}"

  searchPathRef.set [← getLibDir sysroot]
  enableInitializersExecution
  let coreEnv ← importModules (loadExts := true) #[{ module := `Lean }] {} 0
  let thmNames := thmArgs.map String.toName
  let (_, chalDefs) := collectChallengeDefs envC thmNames {} #[]
  let allRoots := (chalDefs.map Prod.snd) ++ thmNames.toArray
  let (_, trustedEnv, _) ← StateT.run (allRoots.forM (addTypeProxy envC)) (coreEnv, {})
  let mut auditRows : Array CoreAuditRow := #[]
  let mut totalBytes := 0
  for (k, d) in chalDefs.reverse do
    let declTxt ← printCoreDecl envC trustedEnv k d
    totalBytes := totalBytes + declTxt.utf8ByteSize
    if totalBytes > 512 * 1024 then
      throw <| IO.userError "audit declarations exceed the 512 KiB limit"
    auditRows := auditRows.push { name := d.toString, kind := k, declaration := declTxt }
  for raw in thmArgs do
    let t := raw.toName
    if coreEnv.contains t then
      throw <| IO.userError s!"audit declaration collides with a trusted Lean constant: {raw}"
    let declTxt ← printCoreDecl envC trustedEnv "theorem" t
    totalBytes := totalBytes + declTxt.utf8ByteSize
    if totalBytes > 512 * 1024 then
      throw <| IO.userError "audit declarations exceed the 512 KiB limit"
    auditRows := auditRows.push { name := raw, kind := "theorem", declaration := declTxt }
  IO.FS.writeFile (System.FilePath.mk ".verification/core_notation_audit.json") ((toJson auditRows).pretty ++ "\\n")
  return 0
"""


FC_COMPARE_LEAN = """module

import Lean
open Lean

set_option linter.unusedVariables false

structure FCAuditRow where
  source : String
  target_declaration : String
  solution_declaration : String
  match_mode : String
  status : String
deriving ToJson, FromJson

def strToName (s : String) : Name :=
  (s.splitOn ".").foldl Name.mkStr Name.anonymous

def isExternalMathlibRoot (r : Name) : Bool :=
  r == `Mathlib || r == `Init || r == `Std || r == `Batteries || r == `Lean ||
  r == `Qq || r == `Aesop || r == `ProofWidgets || r == `ImportGraph ||
  r == `Plausible || r == `LeanSearchClient

def modToRelOlean (m : Name) : System.FilePath :=
  let parts := m.components.map Name.toString
  System.mkFilePath parts |>.addExtension "olean"

def findModuleOlean? (dirs : List System.FilePath) (m : Name) : IO (Option System.FilePath) := do
  let rel := modToRelOlean m
  for d in dirs do
    let cand := d / rel
    if (← cand.pathExists) then
      return some cand
  return none

abbrev LocalConstMap := Std.HashMap Name ConstantInfo

partial def loadModuleClosure
    (dirs : List System.FilePath)
    (seenMods : NameSet)
    (cmap : LocalConstMap)
    (regs : Array CompactedRegion)
    (work : List (Name × System.FilePath)) : IO (NameSet × LocalConstMap × Array CompactedRegion) := do
  match work with
  | [] => return (seenMods, cmap, regs)
  | (mName, fp) :: rest =>
    if seenMods.contains mName then
      loadModuleClosure dirs seenMods cmap regs rest
    else
      let seenMods := seenMods.insert mName
      if !(← fp.pathExists) then
        loadModuleClosure dirs seenMods cmap regs rest
      else
        let (md, reg) ← readModuleData fp
        let mut cmap2 := cmap
        for ci in md.constants do
          cmap2 := cmap2.insert ci.name ci
        let mut nextWork := rest
        for imp in md.imports do
          let r := imp.module.getRoot
          if !isExternalMathlibRoot r && !seenMods.contains imp.module then
            if let some impFp ← findModuleOlean? dirs imp.module then
              nextWork := (imp.module, impFp) :: nextWork
        loadModuleClosure dirs seenMods cmap2 (regs.push reg) nextWork

def isThmLike (ci : ConstantInfo) : Bool :=
  ci matches .thmInfo _ || ci matches .opaqueInfo _ || ci matches .axiomInfo _

def isStatementDef (ci : ConstantInfo) : Bool :=
  match ci with
  | .defnInfo v => v.type == .sort .zero
  | _ => false

def targetPropOf (ci : ConstantInfo) : Expr :=
  match ci with
  | .defnInfo v => if v.type == .sort .zero then v.value else ci.type
  | _ => ci.type

def instantiateTargetPropZero (ci : ConstantInfo) : Expr :=
  let ls := ci.levelParams.map fun _ => Level.zero
  match ci with
  | .defnInfo v => if v.type == .sort .zero then ci.instantiateValueLevelParams! ls else ci.instantiateTypeLevelParams ls
  | _ => ci.instantiateTypeLevelParams ls

def levelsEquiv (us vs : List Level) : Bool :=
  us.length == vs.length && (us.zip vs).all fun (u, v) => Level.isEquiv u v

def unfoldApp? (cmap : LocalConstMap) (e : Expr) : Option Expr :=
  let args := e.getAppArgs
  match e.getAppFn with
  | .const n us =>
    if n == `GE.ge && args.size >= 4 then
      some (mkAppN (mkApp4 (.const `LE.le us) args[0]! args[1]! args[3]! args[2]!) (args.extract 4 args.size))
    else if n == `GT.gt && args.size >= 4 then
      some (mkAppN (mkApp4 (.const `LT.lt us) args[0]! args[1]! args[3]! args[2]!) (args.extract 4 args.size))
    else if n == `Prod.fst && args.size >= 3 then
      some (mkAppN (.proj `Prod 0 args[2]!) (args.extract 3 args.size))
    else if n == `Prod.snd && args.size >= 3 then
      some (mkAppN (.proj `Prod 1 args[2]!) (args.extract 3 args.size))
    else if n == `Prod.casesOn && args.size >= 5 then
      let p := args[3]!
      let f := args[4]!
      some (Expr.beta f (#[.proj `Prod 0 p, .proj `Prod 1 p] ++ args.extract 5 args.size))
    else if n == `Prod.rec && args.size >= 5 then
      let f := args[3]!
      let p := args[4]!
      some (Expr.beta f (#[.proj `Prod 0 p, .proj `Prod 1 p] ++ args.extract 5 args.size))
    else if n == `Subtype.val && args.size >= 3 then
      some (mkAppN (.proj `Subtype 0 args[2]!) (args.extract 3 args.size))
    else if n == `Subtype.property && args.size >= 3 then
      some (mkAppN (.proj `Subtype 1 args[2]!) (args.extract 3 args.size))
    else if n == `Subtype.casesOn && args.size >= 5 then
      let s := args[3]!
      let f := args[4]!
      some (Expr.beta f (#[.proj `Subtype 0 s, .proj `Subtype 1 s] ++ args.extract 5 args.size))
    else if n == `Subtype.rec && args.size >= 5 then
      let f := args[3]!
      let s := args[4]!
      some (Expr.beta f (#[.proj `Subtype 0 s, .proj `Subtype 1 s] ++ args.extract 5 args.size))
    else
      match cmap.get? n with
      | some (info@(.defnInfo _)) =>
        let body := info.instantiateValueLevelParams! us
        some (Expr.beta body args)
      | _ => none
  | _ => none

partial def whnfHead (e : Expr) : Expr :=
  match e with
  | .mdata _ inner => whnfHead inner
  | .letE _ _ v b _ => whnfHead (b.instantiate1 v)
  | .app f a =>
    let f' := whnfHead f
    if f'.isLambda then
      whnfHead (f'.bindingBody!.instantiate1 a)
    else
      .app f' a
  | _ => e

def isInternalProofApp (mapA mapB : LocalConstMap) (eA eB : Expr) : Option (Name × Name) :=
  match eA.getAppFn, eB.getAppFn with
  | .const n1 _, .const n2 _ =>
    if n1.isInternalDetail && n2.isInternalDetail then
      match mapA.get? n1, mapB.get? n2 with
      | some info1, some info2 =>
        if isThmLike info1 && isThmLike info2 then some (n1, n2) else none
      | _, _ => none
    else
      none
  | _, _ => none

def isAbstractedNestedProof (cmap : LocalConstMap) (e : Expr) : Bool :=
  match e.getAppFn with
  | .const n _ =>
    if n.isInternalDetail && (n.toString.splitOn "._proof_").length > 1 then
      match cmap.get? n with
      | some info => isThmLike info
      | none => false
    else
      false
  | _ => false

def isNonProofDataExpr (cmap : LocalConstMap) (e : Expr) : Bool :=
  match e with
  | .lit _ | .sort _ | .forallE _ _ _ _ => true
  | _ =>
    match e.getAppFn with
    | .const n _ =>
      match cmap.get? n with
      | some (.defnInfo v) => v.type == .sort .zero
      | some (.inductInfo _) | some (.ctorInfo _) => true
      | _ => false
    | _ => false

mutual
partial def checkConstPair (mapA mapB : LocalConstMap) (visited : Std.HashSet (Name × Name)) (nA nB : Name) : IO (Std.HashSet (Name × Name)) := do
  if visited.contains (nA, nB) then
    return visited
  match mapA.get? nA, mapB.get? nB with
  | none, none =>
    if nA == nB then
      return visited.insert (nA, nB)
    else
      throw <| IO.userError s!"Shared upstream constant mismatch: {nA} vs {nB}"
  | some infoA, some infoB =>
    let visited := visited.insert (nA, nB)
    if infoA.levelParams.length != infoB.levelParams.length then
      throw <| IO.userError s!"Level params mismatch: {nA} vs {nB}"
    let ls := infoA.levelParams.map Level.param
    if nA.isInternalDetail && nB.isInternalDetail then
      if isThmLike infoA && isThmLike infoB then
        return visited
    let visited ← checkExprEq mapA mapB visited infoA.type (infoB.instantiateTypeLevelParams ls)
    if isThmLike infoA && isThmLike infoB then
      return visited
    match infoA, infoB with
    | .defnInfo vA, .defnInfo _ =>
      checkExprEq mapA mapB visited vA.value (infoB.instantiateValueLevelParams! ls)
    | .inductInfo iA, .inductInfo iB =>
      if iA.numParams != iB.numParams || iA.numIndices != iB.numIndices || iA.ctors.length != iB.ctors.length then
        throw <| IO.userError s!"Inductive mismatch: {nA} vs {nB}"
      let mut vis := visited
      for (c1, c2) in iA.ctors.zip iB.ctors do
        vis ← checkConstPair mapA mapB vis c1 c2
      return vis
    | .ctorInfo cA, .ctorInfo cB =>
      if cA.cidx != cB.cidx || cA.numParams != cB.numParams || cA.numFields != cB.numFields then
        throw <| IO.userError s!"Ctor mismatch: {nA} vs {nB}"
      checkConstPair mapA mapB visited cA.induct cB.induct
    | .recInfo rA, .recInfo rB =>
      if rA.numParams != rB.numParams || rA.numIndices != rB.numIndices || rA.numMotives != rB.numMotives || rA.numMinors != rB.numMinors || rA.rules.length != rB.rules.length || rA.k != rB.k || rA.all.length != rB.all.length then
        throw <| IO.userError s!"Recursor mismatch: {nA} vs {nB}"
      let mut vis := visited
      for (ind1, ind2) in rA.all.zip rB.all do
        vis ← checkConstPair mapA mapB vis ind1 ind2
      return vis
    | _, _ =>
      throw <| IO.userError s!"Constant kind mismatch: {nA} vs {nB}"
  | _, _ =>
    throw <| IO.userError s!"One constant is local and one is upstream: {nA} vs {nB}"

partial def checkExprEq (mapA mapB : LocalConstMap) (visited : Std.HashSet (Name × Name)) (rawA rawB : Expr) : IO (Std.HashSet (Name × Name)) := do
  let eA := whnfHead rawA
  let eB := whnfHead rawB
  if let some (n1, n2) := isInternalProofApp mapA mapB eA eB then
    return (← checkConstPair mapA mapB visited n1 n2)
  if (isAbstractedNestedProof mapA eA && !isNonProofDataExpr mapB eB) ||
     (isAbstractedNestedProof mapB eB && !isNonProofDataExpr mapA eA) then
    return visited
  match eA.getAppFn, eB.getAppFn with
  | .const n1 us1, .const n2 us2 =>
    if eA.getAppNumArgs == eB.getAppNumArgs && levelsEquiv us1 us2 then
      try
        let mut vis ← checkConstPair mapA mapB visited n1 n2
        for (a1, a2) in eA.getAppArgs.zip eB.getAppArgs do
          vis ← checkExprEq mapA mapB vis a1 a2
        return vis
      catch err =>
        if let some eA' := unfoldApp? mapA eA then
          return (← checkExprEq mapA mapB visited eA' eB)
        else if let some eB' := unfoldApp? mapB eB then
          return (← checkExprEq mapA mapB visited eA eB')
        else throw err
    else
      if let some eA' := unfoldApp? mapA eA then
        return (← checkExprEq mapA mapB visited eA' eB)
      else if let some eB' := unfoldApp? mapB eB then
        return (← checkExprEq mapA mapB visited eA eB')
      else
        throw <| IO.userError s!"App spine mismatch: {n1} ({eA.getAppNumArgs} args) vs {n2} ({eB.getAppNumArgs} args)"
  | .const _ _, _ =>
    if let some eA' := unfoldApp? mapA eA then
      return (← checkExprEq mapA mapB visited eA' eB)
    else
      throw <| IO.userError s!"Head mismatch: {eA} vs {eB}"
  | _, .const _ _ =>
    if let some eB' := unfoldApp? mapB eB then
      return (← checkExprEq mapA mapB visited eA eB')
    else
      throw <| IO.userError s!"Head mismatch: {eA} vs {eB}"
  | _, _ =>
    match eA, eB with
    | .bvar i, .bvar j =>
      if i != j then throw <| IO.userError s!"Bound var mismatch: {i} vs {j}"
      return visited
    | .sort u, .sort v =>
      if !Level.isEquiv u v then throw <| IO.userError s!"Sort mismatch: {u} vs {v}"
      return visited
    | .lit l1, .lit l2 =>
      if l1 != l2 then throw <| IO.userError s!"Literal mismatch"
      return visited
    | .app f1 a1, .app f2 a2 =>
      let vis ← checkExprEq mapA mapB visited f1 f2
      checkExprEq mapA mapB vis a1 a2
    | .lam _ d1 b1 _, .lam _ d2 b2 _ =>
      let vis ← checkExprEq mapA mapB visited d1 d2
      checkExprEq mapA mapB vis b1 b2
    | .forallE _ d1 b1 _, .forallE _ d2 b2 _ =>
      let vis ← checkExprEq mapA mapB visited d1 d2
      checkExprEq mapA mapB vis b1 b2
    | .proj t1 i1 s1, .proj t2 i2 s2 =>
      if i1 != i2 then throw <| IO.userError s!"Proj index mismatch: {i1} vs {i2}"
      let vis ← checkConstPair mapA mapB visited t1 t2
      checkExprEq mapA mapB vis s1 s2
    | _, _ =>
      throw <| IO.userError s!"Expression mismatch:\\n  FC:  {eA}\\n  Sol: {eB}"
end

partial def transformUnderForall (f : Expr → Option Expr) (e : Expr) : Option Expr :=
  match e with
  | .mdata _ inner => transformUnderForall f inner
  | .forallE n d b bi =>
    match f e with
    | some e' => some e'
    | none => (transformUnderForall f b).map fun b' => .forallE n d b' bi
  | _ => f e

def normalizeTopAnswerShapesForType (allowOpenSorry : Bool) (suffix : String) (eFC eS : Expr) : List (String × Expr × Expr) := Id.run do
  let mut out : List (String × Expr × Expr) := [("exact" ++ suffix, eFC, eS)]
  let unwrapIffTrue (e : Expr) : Option Expr :=
    match e.getAppFn, e.getAppArgs with
    | .const `Iff _, #[lhs, rhs] =>
      let lhs0 := match lhs with | .mdata _ inner => inner | _ => lhs
      if lhs0.isConstOf `True then some rhs else none
    | _, _ => none
  let unwrapIffFalseToNot (e : Expr) : Option Expr :=
    match e.getAppFn, e.getAppArgs with
    | .const `Iff _, #[lhs, rhs] =>
      let lhs0 := match lhs with | .mdata _ inner => inner | _ => lhs
      if lhs0.isConstOf `False then some (mkApp (.const `Not []) rhs) else none
    | _, _ => none
  if let some t := transformUnderForall unwrapIffTrue eFC then
    out := out ++ [("iff_true_to_prop" ++ suffix, t, eS)]
  if let some tS := transformUnderForall unwrapIffTrue eS then
    out := out ++ [("prop_to_iff_true" ++ suffix, eFC, tS)]
  if let some t := transformUnderForall unwrapIffFalseToNot eFC then
    out := out ++ [("iff_false_to_not" ++ suffix, t, eS)]
  if let some tS := transformUnderForall unwrapIffFalseToNot eS then
    out := out ++ [("not_to_iff_false" ++ suffix, eFC, tS)]
  if allowOpenSorry then
    let unwrapOpenSorryToTrueIff (e : Expr) : Option Expr :=
      match e.getAppFn, e.getAppArgs with
      | .const `Iff _, #[lhs, rhs] =>
        let lhs0 := match lhs with | .mdata _ inner => inner | _ => lhs
        if lhs0.getAppFn.isConstOf `sorryAx then some (mkApp2 (.const `Iff []) (.const `True []) rhs) else none
      | _, _ => none
    let unwrapOpenSorryToProp (e : Expr) : Option Expr :=
      match e.getAppFn, e.getAppArgs with
      | .const `Iff _, #[lhs, rhs] =>
        let lhs0 := match lhs with | .mdata _ inner => inner | _ => lhs
        if lhs0.getAppFn.isConstOf `sorryAx then some rhs else none
      | _, _ => none
    let unwrapOpenSorryToFalseIff (e : Expr) : Option Expr :=
      match e.getAppFn, e.getAppArgs with
      | .const `Iff _, #[lhs, rhs] =>
        let lhs0 := match lhs with | .mdata _ inner => inner | _ => lhs
        if lhs0.getAppFn.isConstOf `sorryAx then some (mkApp2 (.const `Iff []) (.const `False []) rhs) else none
      | _, _ => none
    let unwrapOpenSorryToNot (e : Expr) : Option Expr :=
      match e.getAppFn, e.getAppArgs with
      | .const `Iff _, #[lhs, rhs] =>
        let lhs0 := match lhs with | .mdata _ inner => inner | _ => lhs
        if lhs0.getAppFn.isConstOf `sorryAx then some (mkApp (.const `Not []) rhs) else none
      | _, _ => none
    if let some t := transformUnderForall unwrapOpenSorryToTrueIff eFC then
      out := out ++ [("resolves_open_answer_true_iff" ++ suffix, t, eS)]
    if let some t := transformUnderForall unwrapOpenSorryToProp eFC then
      out := out ++ [("resolves_open_answer_true_prop" ++ suffix, t, eS)]
    if let some t := transformUnderForall unwrapOpenSorryToFalseIff eFC then
      out := out ++ [("resolves_open_answer_false_iff" ++ suffix, t, eS)]
    if let some t := transformUnderForall unwrapOpenSorryToNot eFC then
      out := out ++ [("resolves_open_answer_false_not" ++ suffix, t, eS)]
  return out

def normalizeTopAnswerShapes (allowOpenSorry : Bool) (infoFC infoS : ConstantInfo) : List (String × Expr × Expr) :=
  let eS := targetPropOf infoS
  let base := normalizeTopAnswerShapesForType allowOpenSorry "" (targetPropOf infoFC) eS
  if !infoFC.levelParams.isEmpty && infoS.levelParams.isEmpty then
    let eFC0 := instantiateTargetPropZero infoFC
    base ++ normalizeTopAnswerShapesForType allowOpenSorry "_univ_zero" eFC0 eS
  else
    base

def normalizeClaimedKey (s : String) : String :=
  let parts := s.splitOn "."
  let probNum := match parts with
    | p0 :: _ => if p0.startsWith "Erdos" then (p0.drop 5).toString else ""
    | [] => ""
  let tail := match parts with
    | p0 :: p1 :: rest =>
      if p0.startsWith "Erdos" && (p1 == "Palomar" || p1 == "Standalone" || p1 == "Challenge") then
        String.intercalate "_" rest
      else if p0.startsWith "Erdos" then
        String.intercalate "_" (p1 :: rest)
      else
        String.intercalate "_" parts
    | _ => s.replace "." "_"
  let tail :=
    if tail == "statement" && probNum != "" then
      s!"erdos_{probNum}"
    else if tail.startsWith "statement_" then
      (tail.drop 10).toString
    else
      tail
  let tail := if tail.startsWith "not_" then (tail.drop 4).toString else tail
  tail

public unsafe def main (args : List String) : IO UInt32 := do
  let runMode := args[0]!
  let targetOlean := System.FilePath.mk args[1]!
  let solOlean := System.FilePath.mk args[2]!
  let sourceLabel := args[3]!
  let outJsonPath := System.FilePath.mk args[4]!
  let restArgs := args.drop 5
  let envLeanPath := (← IO.getEnv "LEAN_PATH").getD ""
  let envDirs := (envLeanPath.splitOn ":").filter (· != "") |>.map System.FilePath.mk
  let tDir0 := targetOlean.parent.getD "."
  let tDir1 := tDir0.parent.getD tDir0
  let tDir2 := tDir1.parent.getD tDir1
  let dirs := (solOlean.parent.getD ".") :: tDir0 :: tDir1 :: tDir2 :: envDirs
  let (_, mapTarget, r1) ← loadModuleClosure dirs {} {} #[] [(`TargetMod, targetOlean)]
  let (_, mapSol, r2) ← loadModuleClosure dirs {} {} r1 [(`SolMod, solOlean)]
  let mut regs := r2
  let mut existingRows : Array FCAuditRow := #[]
  if (← outJsonPath.pathExists) then
    if let .ok jTxt ← IO.FS.readFile outJsonPath |>.toBaseIO then
      if let .ok jVal := Json.parse jTxt then
        if let .ok parsed := @fromJson? (Array FCAuditRow) _ jVal then
          existingRows := parsed
  if runMode == "pairs" then
    for rawPair in restArgs do
      let parts := rawPair.splitOn ":"
      let fcThm := strToName parts[0]!
      let solThm := strToName parts[1]!
      let some infoFC := mapTarget.get? fcThm
        | throw <| IO.userError s!"Missing target declaration {fcThm} in {targetOlean}"
      let some infoS := mapSol.get? solThm
        | throw <| IO.userError s!"Missing solution declaration {solThm} in {solOlean}"
      let mut matched := false
      let mut firstErr := ""
      for (mode, tA, tB) in normalizeTopAnswerShapes true infoFC infoS do
        if !matched then
          try
            let _ ← checkExprEq mapTarget mapSol {} tA tB
            IO.println s!"FC_MATCH|{sourceLabel}|{fcThm}|{solThm}|{mode}"
            existingRows := existingRows.push {
              source := sourceLabel
              target_declaration := fcThm.toString
              solution_declaration := solThm.toString
              match_mode := mode
              status := "PASS"
            }
            matched := true
          catch err =>
            if firstErr == "" then
              firstErr := toString err
      if !matched then
        throw <| IO.userError s!"Statement mismatch between {fcThm} and {solThm}:\\n{firstErr}"
  else
    let (tMd, regT) ← readModuleData targetOlean
    let (sMd, regS) ← readModuleData solOlean
    regs := (regs.push regT).push regS
    let probPrefix :=
      if sourceLabel.startsWith "FormalConjectures.ErdosProblems." then
        let pnum := sourceLabel.drop ("FormalConjectures.ErdosProblems.".length)
        some (s!"Erdos{pnum}.", s!"erdos_{pnum}")
      else
        none
    let targetCands := tMd.constants.filter fun ci =>
      let nameStr := ci.name.toString
      let inProbScope := match probPrefix with
        | some (nsPref, thmSub) => nameStr.startsWith nsPref || (nameStr.splitOn thmSub).length > 1
        | none => true
      !ci.name.isInternalDetail && inProbScope && (isThmLike ci || isStatementDef ci)
    let solThmNames := restArgs.map strToName
    let mut solCands : Array ConstantInfo := #[]
    let mut seenSol : NameSet := {}
    for n in solThmNames do
      if let some ci := mapSol.get? n then
        solCands := solCands.push ci
        seenSol := seenSol.insert n
    for ci in sMd.constants do
      if !ci.name.isInternalDetail && (isThmLike ci || isStatementDef ci) && !seenSol.contains ci.name then
        solCands := solCands.push ci
        seenSol := seenSol.insert ci.name
    for infoFC in targetCands do
      let fcKey := normalizeClaimedKey infoFC.name.toString
      let mut fcMatchedAny := false
      let mut claimedErr : Option (Name × String) := none
      for infoS in solCands do
        let solKey := normalizeClaimedKey infoS.name.toString
        let isSameKey := fcKey != "" && fcKey != "statement" && fcKey == solKey
        let mut matched := false
        let mut firstPairErr := ""
        for (mode, tA, tB) in normalizeTopAnswerShapes true infoFC infoS do
          if !matched then
            try
              let _ ← checkExprEq mapTarget mapSol {} tA tB
              IO.println s!"FC_MATCH|{sourceLabel}|{infoFC.name}|{infoS.name}|{mode}"
              existingRows := existingRows.push {
                source := sourceLabel
                target_declaration := infoFC.name.toString
                solution_declaration := infoS.name.toString
                match_mode := mode
                status := "PASS"
              }
              matched := true
              fcMatchedAny := true
            catch err =>
              if firstPairErr == "" then
                firstPairErr := toString err
        if !matched && isSameKey && claimedErr.isNone then
          claimedErr := some (infoS.name, firstPairErr)
      if !fcMatchedAny then
        if let some (solName, errMsg) := claimedErr then
          throw <| IO.userError s!"Claimed theorem {solName} failed statement-equivalence check against {infoFC.name} ({sourceLabel}):\\n{errMsg}"
  if outJsonPath.toString != "" then
    IO.FS.writeFile outJsonPath ((toJson existingRows).pretty ++ "\\n")
  return if regs.isEmpty then 1 else 0
"""


COMPARATOR_ALLOWED_KEYS = {
    "challenge_module",
    "solution_module",
    "theorem_names",
    "definition_names",
    "permitted_axioms",
    "enable_nanoda",
}


def load_json_unique(path: pathlib.Path) -> Any:
    def _unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        obj: dict[str, Any] = {}
        dups: list[str] = []
        for k, v in pairs:
            if k in obj:
                dups.append(k)
            obj[k] = v
        if dups:
            raise ValueError(f"duplicate JSON key(s): {sorted(set(dups))}")
        return obj

    return json.loads(path.read_text(encoding="utf-8"), object_pairs_hook=_unique_object)


def strip_lean_comments(text: str) -> str:
    out: list[str] = []
    i = 0
    n = len(text)
    block_depth = 0
    in_string = False
    while i < n:
        ch = text[i]
        if block_depth > 0:
            if text.startswith("/-", i):
                block_depth += 1
                out.append("  ")
                i += 2
            elif text.startswith("-/", i):
                block_depth -= 1
                out.append("  ")
                i += 2
            else:
                out.append("\n" if ch == "\n" else " ")
                i += 1
        elif in_string:
            if ch == "\\" and i + 1 < n:
                out.append("  ")
                i += 2
            elif ch == '"':
                in_string = False
                out.append(" ")
                i += 1
            else:
                out.append("\n" if ch == "\n" else " ")
                i += 1
        else:
            if text.startswith("/-", i):
                block_depth = 1
                out.append("  ")
                i += 2
            elif text.startswith("--", i):
                while i < n and text[i] != "\n":
                    out.append(" ")
                    i += 1
            elif ch == '"':
                in_string = True
                out.append(" ")
                i += 1
            else:
                out.append(ch)
                i += 1
    return "".join(out)


def all_packages() -> list[str]:
    return sorted(
        p.name
        for p in REPO_ROOT.glob("erdos-*")
        if p.is_dir() and re.fullmatch(r"erdos-\d+", p.name)
        and (p / "comparator.json").is_file()
    )


def check_package_manifest(pkg: str) -> list[str]:
    errors: list[str] = []
    pkg_dir = REPO_ROOT / pkg
    if not pkg_dir.is_dir():
        return [f"{pkg}: directory does not exist"]

    required_files = [
        "Challenge.lean",
        "Solution.lean",
        "AxiomAudit.lean",
        "comparator.json",
        "formalization.yaml",
        "lakefile.toml",
        "lake-manifest.json",
        "lean-toolchain",
        "LICENSE",
        "README.md",
        "BUILD.md",
        "THIRD_PARTY.md",
        "verify.sh",
    ]
    for req in required_files:
        fpath = pkg_dir / req
        if not fpath.is_file():
            errors.append(f"{pkg}: missing required file {req}")

    verify_sh = pkg_dir / "verify.sh"
    if verify_sh.is_file() and not os.access(verify_sh, os.X_OK):
        errors.append(f"{pkg}: verify.sh is not executable")

    lic_path = pkg_dir / "LICENSE"
    if lic_path.is_file():
        lic_txt = lic_path.read_text(encoding="utf-8", errors="replace")
        if "Apache License" not in lic_txt:
            errors.append(f"{pkg}: LICENSE is not the Apache-2.0 license")

    tc_path = pkg_dir / "lean-toolchain"
    if tc_path.is_file():
        tc = tc_path.read_text(encoding="utf-8").strip()
        if tc != EXPECTED_TOOLCHAIN:
            errors.append(f"{pkg}: lean-toolchain is {tc!r}, expected {EXPECTED_TOOLCHAIN!r}")

    chal_path = pkg_dir / "Challenge.lean"
    if chal_path.is_file():
        chal_raw = chal_path.read_text(encoding="utf-8", errors="replace")
        chal_lines = len(chal_raw.splitlines())
        chal_bytes = chal_path.stat().st_size
        if chal_lines > 1000:
            errors.append(f"{pkg}: Challenge.lean exceeds Palomar 1,000-line cap ({chal_lines} lines)")
        if chal_bytes > 100 * 1024:
            errors.append(f"{pkg}: Challenge.lean exceeds Palomar 100 KiB cap ({chal_bytes} bytes)")
        if chal_lines > 300 or chal_bytes > 32 * 1024:
            print(
                f"WARN: {pkg}: Challenge.lean ({chal_lines} lines, {chal_bytes} bytes) exceeds Palomar preferred 300-line / 32 KiB review surface",
                file=sys.stderr,
            )
        chal_clean = strip_lean_comments(chal_path.read_text(encoding="utf-8", errors="replace"))
        for line in chal_clean.splitlines():
            m = re.match(r"^\s*(?:public\s+|private\s+)?(?:meta\s+)?import\s+(?:all\s+)?(.+)$", line)
            if m:
                for mod in m.group(1).split():
                    if not (mod == "Mathlib" or mod.startswith("Mathlib.")):
                        errors.append(f"{pkg}: Challenge.lean must import only Mathlib (found {mod!r})")

    sol_path = pkg_dir / "Solution.lean"
    if sol_path.is_file():
        sol_clean = strip_lean_comments(sol_path.read_text(encoding="utf-8", errors="replace"))
        for line in sol_clean.splitlines():
            m_sol = re.match(r"^\s*(?:public\s+|private\s+)?(?:meta\s+)?import\s+(?:all\s+)?(.+)$", line)
            if m_sol and "Challenge" in m_sol.group(1).split():
                errors.append(f"{pkg}: Solution.lean must not import Challenge")

    manifest_path = pkg_dir / "lake-manifest.json"
    lakefile_path = pkg_dir / "lakefile.toml"
    lf_name: str | None = None
    if lakefile_path.is_file():
        try:
            lf = tomllib.loads(lakefile_path.read_text(encoding="utf-8"))
            lf_name = lf.get("name")
            lean_libs = lf.get("lean_lib", [])
            libs = {lib.get("name") for lib in lean_libs}
            for req_lib in ("Challenge", "Solution", "AxiomAudit"):
                if req_lib not in libs:
                    errors.append(f"{pkg}: lakefile.toml missing lean_lib target {req_lib!r}")
            if (pkg_dir / "Statement.lean").is_file() and "Statement" not in libs:
                errors.append(f"{pkg}: Statement.lean exists but lakefile.toml is missing lean_lib target 'Statement'")
            for lib in lean_libs:
                lib_name = lib.get("name", "<unnamed>")
                more_args = lib.get("moreLeanArgs", [])
                if lib_name == "Challenge":
                    if "hasSorry" in more_args:
                        errors.append(f"{pkg}: lakefile.toml Challenge target must not set -E hasSorry")
                else:
                    if "-E" not in more_args or "hasSorry" not in more_args:
                        errors.append(f"{pkg}: lakefile.toml lean_lib {lib_name!r} must include '-E' and 'hasSorry' in moreLeanArgs")
            reqs = {r.get("name"): r.get("rev") for r in lf.get("require", [])}
            if set(reqs.keys()) != {"mathlib"}:
                errors.append(f"{pkg}: lakefile.toml must require only 'mathlib' (found {sorted(reqs.keys())})")
            if reqs.get("mathlib") != EXPECTED_MATHLIB_REV:
                errors.append(f"{pkg}: lakefile.toml mathlib rev is not {EXPECTED_MATHLIB_REV}")
        except Exception as exc:
            errors.append(f"{pkg}: invalid lakefile.toml ({exc})")

    if manifest_path.is_file():
        try:
            manifest = load_json_unique(manifest_path)
            mathlib_pkgs = [
                entry for entry in manifest.get("packages", []) if entry.get("name") == "mathlib"
            ]
            if not mathlib_pkgs or mathlib_pkgs[0].get("rev") != EXPECTED_MATHLIB_REV:
                errors.append(
                    f"{pkg}: lake-manifest.json mathlib rev is not {EXPECTED_MATHLIB_REV}"
                )
            if lf_name and manifest.get("name") and manifest.get("name") != lf_name:
                errors.append(
                    f"{pkg}: lake-manifest.json name {manifest.get('name')!r} does not match lakefile.toml name {lf_name!r}"
                )
        except Exception as exc:
            errors.append(f"{pkg}: invalid lake-manifest.json ({exc})")

    comp_path = pkg_dir / "comparator.json"
    fy_path = pkg_dir / "formalization.yaml"
    aud_path = pkg_dir / "AxiomAudit.lean"
    if comp_path.is_file() and fy_path.is_file():
        try:
            comp = load_json_unique(comp_path)
            fy = load_json_unique(fy_path)
            unknown_comp_keys = set(comp.keys()) - COMPARATOR_ALLOWED_KEYS
            if unknown_comp_keys:
                errors.append(
                    f"{pkg}: comparator.json has disallowed/unknown keys: {sorted(unknown_comp_keys)}"
                )
            comp_theorems = comp.get("theorem_names", [])
            if not comp_theorems:
                errors.append(f"{pkg}: comparator.json theorem_names is empty")
            if len(comp_theorems) != len(set(comp_theorems)):
                errors.append(f"{pkg}: comparator.json theorem_names contains duplicates")
            if comp.get("challenge_module") != "Challenge" or comp.get("solution_module") != "Solution":
                errors.append(f"{pkg}: comparator.json must set challenge_module='Challenge' and solution_module='Solution'")
            if comp.get("enable_nanoda") is not True:
                errors.append(f"{pkg}: comparator.json must set enable_nanoda=true")
            perm_axs = comp.get("permitted_axioms", [])
            if not perm_axs or any(a not in PERMITTED_AXIOMS for a in perm_axs):
                errors.append(f"{pkg}: comparator.json permitted_axioms must be a subset of {PERMITTED_AXIOMS}")
            if fy.get("version") != "v0.4":
                errors.append(
                    f"{pkg}: formalization.yaml version is {fy.get('version')!r}, expected 'v0.4'"
                )
            proj = fy.get("project", {})
            proj_name = proj.get("name", "")
            if not isinstance(proj_name, str) or not (1 <= len(proj_name.strip()) <= 300):
                errors.append(f"{pkg}: formalization.yaml project.name must be 1..300 characters")
            proj_desc = proj.get("description", "")
            if not isinstance(proj_desc, str) or not (1 <= len(proj_desc.strip()) <= 10000):
                errors.append(f"{pkg}: formalization.yaml project.description must be 1..10,000 characters")
            if proj.get("authors") != ["Linmiao Xu"] or proj.get("responsible_maintainers") != ["Linmiao Xu"]:
                errors.append(
                    f"{pkg}: formalization.yaml project.authors and responsible_maintainers must be ['Linmiao Xu']"
                )
            if proj.get("license") != "Apache-2.0":
                errors.append(
                    f"{pkg}: formalization.yaml project.license is {proj.get('license')!r}, expected 'Apache-2.0'"
                )
            cls = fy.get("classification", {})
            arxiv_cats = cls.get("arxiv", [])
            if not isinstance(arxiv_cats, list) or not (1 <= len(arxiv_cats) <= 8):
                errors.append(f"{pkg}: formalization.yaml classification.arxiv must list 1..8 categories")
            msc_codes = cls.get("msc2020", [])
            if not isinstance(msc_codes, list) or len(msc_codes) > 8 or len(msc_codes) != len(set(msc_codes)):
                errors.append(f"{pkg}: formalization.yaml classification.msc2020 must list at most 8 distinct codes")
            rev_status = fy.get("review", {}).get("status", "")
            if not isinstance(rev_status, str) or not rev_status.strip():
                errors.append(f"{pkg}: formalization.yaml review.status must be non-empty")
            methods = fy.get("automation", {}).get("methods", [])
            if not methods or methods[0].get("method") != "agent":
                errors.append(f"{pkg}: formalization.yaml automation.methods[0].method must be 'agent'")
            sources = fy.get("sources", [])
            if not any(s.get("relationship") in VALID_SOURCE_RELS for s in sources):
                errors.append(
                    f"{pkg}: formalization.yaml needs a source with relationship in {sorted(VALID_SOURCE_RELS)}"
                )
            if any(s.get("type") == "original-proof" for s in sources) and any(
                s.get("relationship") in VALID_SOURCE_RELS for s in sources
            ):
                errors.append(
                    f"{pkg}: formalization.yaml cannot mix type='original-proof' with source-based relationships"
                )
            status = fy.get("status", {})
            if status.get("sorry_count", 0) != 0 or status.get("sorry_in_definitions", 0) != 0:
                errors.append(f"{pkg}: formalization.yaml status must have sorry_count=0 and sorry_in_definitions=0")
            main_results = [m.get("declaration") for m in status.get("main_results", [])]
            if main_results != comp_theorems:
                errors.append(
                    f"{pkg}: formalization.yaml status.main_results does not match comparator.json theorem_names"
                )
            if aud_path.is_file():
                aud_clean = strip_lean_comments(aud_path.read_text(encoding="utf-8", errors="replace"))
                aud_imports: list[str] = []
                for line in aud_clean.splitlines():
                    m_imp = re.match(r"^\s*(?:public\s+|private\s+)?(?:meta\s+)?import\s+(?:all\s+)?(.+)$", line)
                    if m_imp:
                        aud_imports.extend(m_imp.group(1).split())
                if "Solution" not in aud_imports:
                    errors.append(f"{pkg}: AxiomAudit.lean must import Solution")
                if "Challenge" in aud_imports:
                    errors.append(f"{pkg}: AxiomAudit.lean must not import Challenge")
                printed = [
                    m.group(1)
                    for m in re.finditer(r"^[ \t]*#print[ \t]+axioms[ \t]+([^\s]+)", aud_clean, re.M)
                ]
                printed_set = set(printed)
                for thm in comp_theorems:
                    if not any(p == thm or thm.endswith("." + p) for p in printed_set):
                        errors.append(f"{pkg}: AxiomAudit.lean missing '#print axioms {thm}'")
                if verify_sh.is_file():
                    ver_txt = verify_sh.read_text(encoding="utf-8", errors="replace")
                    print_axioms_count = len(printed)
                    m_rep = re.search(r"reports\s*!=\s*(\d+)", ver_txt)
                    if m_rep and int(m_rep.group(1)) != print_axioms_count:
                        errors.append(
                            f"{pkg}: verify.sh checks 'reports != {m_rep.group(1)}' but AxiomAudit.lean has {print_axioms_count} '#print axioms' lines"
                        )
                    if not re.search(r"reports\s*!=\s*(?:\d+|expected)", ver_txt):
                        errors.append(f"{pkg}: verify.sh must verify expected axiom report count")
                    if "does not depend on any axioms" not in ver_txt:
                        errors.append(
                            f"{pkg}: verify.sh awk check must handle 'does not depend on any axioms'"
                        )
                    if "--no-sandbox" not in ver_txt or "comparator.log" not in ver_txt:
                        errors.append(
                            f"{pkg}: verify.sh must support --no-sandbox and write .verification/comparator.log"
                        )
                    if "find " not in ver_txt:
                        errors.append(f"{pkg}: verify.sh must use 'find' to check all .lean files")
                    if (pkg_dir / "Statement.lean").is_file() and "Statement" not in ver_txt:
                        errors.append(f"{pkg}: Statement.lean exists but verify.sh does not build Statement")
        except Exception as exc:
            errors.append(f"{pkg}: failed to parse comparator.json or formalization.yaml ({exc})")

    allowed_root_lean = {"Challenge.lean", "Solution.lean", "AxiomAudit.lean", "Statement.lean"}
    mod_to_imports: dict[str, list[str]] = {}
    imp_re = re.compile(r"^\s*(?:public\s+|private\s+)?(?:meta\s+)?import\s+(?:all\s+)?(.+)$", re.M)

    if (pkg_dir / "third_party" / "mathlib").is_dir():
        errors.append(f"{pkg}: forbidden vendored third_party/mathlib directory found")

    for root, dirs, files in os.walk(pkg_dir):
        dirs[:] = [d for d in dirs if d not in SKIP_DIRS and not d.startswith(".lake-") and not d.startswith(".verification-")]
        root_path = pathlib.Path(root)
        for fname in files:
            fpath = root_path / fname
            rel = fpath.relative_to(REPO_ROOT)
            if fpath.is_symlink():
                errors.append(f"{rel}: symbolic links are not permitted in Palomar packages")
                continue
            if fname == ".DS_Store" or fname.endswith(FORBIDDEN_SUFFIXES):
                errors.append(f"{rel}: forbidden temporary or build file")
                continue
            try:
                txt = fpath.read_bytes().decode("utf-8")
            except UnicodeDecodeError:
                errors.append(f"{rel}: file is not valid UTF-8")
                continue
            if fpath.suffix == ".lean":
                lines = txt.splitlines()
                if not lines or lines[0].strip() != "module":
                    errors.append(f"{rel}: first line must be 'module'")
                if len(lines) > 10000:
                    errors.append(f"{rel}: exceeds 10,000 lines ({len(lines)})")
                rel_pkg = fpath.relative_to(pkg_dir).as_posix()
                rel_parts = fpath.relative_to(pkg_dir).parts
                if len(rel_parts) == 1:
                    if fname not in allowed_root_lean:
                        errors.append(f"{rel}: unexpected top-level .lean file (put proof modules under Proofs/)")
                    mod_name = fpath.stem
                elif rel_parts[0] == "Proofs":
                    mod_name = ".".join(fpath.relative_to(pkg_dir / "Proofs").with_suffix("").parts)
                else:
                    errors.append(f"{rel}: .lean files must be at package root or under Proofs/")
                    mod_name = ".".join(fpath.relative_to(pkg_dir).with_suffix("").parts)
                clean_lean = strip_lean_comments(txt)
                if rel_pkg != "Challenge.lean":
                    pat = r"(?<!\.)\b(?:sorry|admit)\b" if rel_pkg == "Proofs/Architect/Tactic.lean" else r"(?<!\.)\b(?:sorry|admit|sorry_using)\b"
                    if re.search(pat, clean_lean):
                        errors.append(f"{rel}: proof file contains 'sorry' or 'admit'")
                imports: list[str] = []
                for m_imp in imp_re.finditer(clean_lean):
                    imports.extend(m_imp.group(1).split())
                mod_to_imports[mod_name] = imports

    reachable_mods: set[str] = set()
    work = [m for m in ("Challenge", "Solution", "AxiomAudit", "Statement") if m in mod_to_imports]
    while work:
        cur = work.pop()
        if cur in reachable_mods:
            continue
        reachable_mods.add(cur)
        for imp in mod_to_imports.get(cur, []):
            if imp in mod_to_imports and imp not in reachable_mods:
                work.append(imp)
    unreached = sorted(set(mod_to_imports) - reachable_mods)
    if unreached:
        errors.append(f"{pkg}: unreferenced .lean module(s) not imported by Challenge/Solution/AxiomAudit/Statement: {unreached}")

    return errors


def detect_changed_packages(
    event_name: str,
    base_sha: str,
    head_sha: str,
    problems_input: str,
    base_ref: str = "",
) -> list[str]:
    valid_pkgs = set(all_packages())
    if problems_input.strip():
        raw = problems_input.strip()
        if raw.lower() == "all":
            return sorted(valid_pkgs)
        selected = []
        for token in raw.split(","):
            tok = token.strip()
            if not tok:
                continue
            if tok.isdigit():
                tok = f"erdos-{tok}"
            if tok not in valid_pkgs:
                raise SystemExit(f"Unknown package: {tok}")
            selected.append(tok)
        return sorted(set(selected))

    if event_name == "workflow_dispatch":
        return []

    changed_lines: list[str] = []
    diff_succeeded = False
    diff_specs: list[str] = []
    if head_sha:
        if base_sha and set(base_sha) != {"0"}:
            if event_name == "pull_request":
                diff_specs.extend([f"{base_sha}...{head_sha}", f"{base_sha}..{head_sha}"])
            else:
                diff_specs.append(f"{base_sha}..{head_sha}")
        if event_name == "pull_request" and base_ref:
            diff_specs.extend([f"origin/{base_ref}...{head_sha}", f"origin/{base_ref}..{head_sha}"])
        if event_name == "push":
            diff_specs.append(f"origin/main...{head_sha}")

    for spec in diff_specs:
        try:
            out = subprocess.check_output(
                ["git", "-C", str(REPO_ROOT), "diff", "--name-only", spec],
                text=True,
                stderr=subprocess.DEVNULL,
            )
            changed_lines = out.splitlines()
            diff_succeeded = True
            if changed_lines or "..." not in spec:
                break
        except subprocess.CalledProcessError:
            pass

    if not diff_succeeded:
        try:
            out = subprocess.check_output(
                ["git", "-C", str(REPO_ROOT), "show", "-m", "--first-parent", "--name-only", "--format=", "HEAD"],
                text=True,
            )
            changed_lines = out.splitlines()
        except subprocess.CalledProcessError:
            changed_lines = []

    touched = set()
    for line in changed_lines:
        parts = pathlib.Path(line.strip()).parts
        if not parts:
            continue
        if parts[0] in valid_pkgs:
            if len(parts) == 2 and parts[1] in DOC_ONLY_FILENAMES:
                continue
            if len(parts) == 3 and parts[1] == "third_party" and (parts[2] == "LICENSE" or parts[2].endswith((".txt", ".md"))):
                continue
            touched.add(parts[0])

    return sorted(touched)


def parse_axioms_log(axioms_log: pathlib.Path) -> list[tuple[str, list[str]]]:
    if not axioms_log.is_file():
        return []
    text = re.sub(r"\s+", " ", axioms_log.read_text(encoding="utf-8", errors="replace"))
    report_re = re.compile(
        r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)"
    )
    results: list[tuple[str, list[str]]] = []
    for match in report_re.finditer(text):
        decl = match.group(1).strip()
        raw_axs = match.group(2)
        axioms = [a.strip() for a in raw_axs.split(",") if a.strip()] if raw_axs is not None else []
        results.append((decl, axioms))
    return results


def sha256_file(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def collect_input_sha256(pkg_dir: pathlib.Path) -> dict[str, str]:
    digests: dict[str, str] = {}
    tracked = [
        "Challenge.lean",
        "Solution.lean",
        "AxiomAudit.lean",
        "Statement.lean",
        "comparator.json",
        "formalization.yaml",
        "lakefile.toml",
        "lake-manifest.json",
        "lean-toolchain",
        "LICENSE",
        "verify.sh",
    ]
    for rel in tracked:
        p = pkg_dir / rel
        if p.is_file():
            digests[rel] = sha256_file(p)
    proofs_dir = pkg_dir / "Proofs"
    if proofs_dir.is_dir():
        for p in sorted(proofs_dir.rglob("*.lean")):
            if p.is_file():
                digests[p.relative_to(pkg_dir).as_posix()] = sha256_file(p)
    return digests


def collect_tool_digests(pkg_dir: pathlib.Path) -> dict[str, str]:
    digests: dict[str, str] = {}
    try:
        prefix_str = subprocess.check_output(
            ["lake", "env", "lean", "--print-prefix"],
            cwd=pkg_dir,
            text=True,
            stderr=subprocess.DEVNULL,
        ).strip()
        prefix = pathlib.Path(prefix_str)
        for tool in ("lake", "lean", "leanexport", "leanchecker", "nanoda_bin", "con-ron"):
            tpath = prefix / "bin" / tool
            if tpath.is_file():
                digests[tool] = sha256_file(tpath.resolve())
    except Exception:
        pass
    bwrap_bin = shutil.which("bwrap")
    if bwrap_bin:
        try:
            digests["bwrap"] = sha256_file(pathlib.Path(bwrap_bin).resolve())
        except Exception:
            pass
    return digests


FC_UTIL_SHIM_HEADER = """module
public meta import Lean
public import Mathlib

set_option autoImplicit false

@[expose] public section

scoped[EuclideanGeometry] notation "ℝ^" n:65 => EuclideanSpace ℝ (Fin n)
scoped[EuclideanGeometry] notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
scoped[EuclideanGeometry] notation "ℝ³" => EuclideanSpace ℝ (Fin 3)
open scoped EuclideanGeometry

section FCShim
open Lean Elab Meta Term

syntax (name := fcAnswerStx) "answer(" term ")" : term

@[term_elab fcAnswerStx]
public meta def elabFCAnswer : TermElab := fun stx expectedType? => do
  match stx with
  | `(answer($a:term)) =>
    if a.raw.isIdent && a.raw.getId == `sorry then
      let ty ← match expectedType? with
        | some t => pure t
        | none => Meta.mkFreshTypeMVar
      let e ← Meta.mkSorry ty (synthetic := false)
      return mkAnnotation `answer e
    else
      let e ← elabTerm a expectedType?
      return mkAnnotation `answer e
  | _ => throwUnsupportedSyntax
end FCShim
"""


def compute_package_state_sha256(pkg: str, input_sha256: dict[str, str]) -> str:
    canonical = json.dumps(
        {
            "package": pkg,
            "lean_toolchain": EXPECTED_TOOLCHAIN,
            "mathlib_revision": EXPECTED_MATHLIB_REV,
            "input_sha256": dict(sorted(input_sha256.items())),
        },
        sort_keys=True,
        separators=(",", ":"),
    )
    return hashlib.sha256(canonical.encode("utf-8")).hexdigest()


def resolve_package_commit_and_id(
    pkg: str,
    fallback_commit: str,
    state_sha256: str,
) -> tuple[str, str, str]:
    """Return (package_commit, commit_date_utc, verification_id) formatted as YYYY-MM-DD-<pkg_commit[:8]>."""
    git_env = os.environ.copy()
    git_env["TZ"] = "UTC"
    git_env["GIT_NO_LAZY_FETCH"] = "1"
    candidates = [fallback_commit.strip(), "HEAD"] if fallback_commit.strip() else ["HEAD"]
    valid_refs: list[str] = []
    for ref in candidates:
        if ref in valid_refs:
            continue
        if subprocess.run(
            ["git", "--no-lazy-fetch", "-C", str(REPO_ROOT), "cat-file", "-e", f"{ref}^{{commit}}"],
            env=git_env,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        ).returncode == 0:
            valid_refs.append(ref)

    for ref in valid_refs:
        try:
            out = subprocess.check_output(
                [
                    "git",
                    "--no-lazy-fetch",
                    "-C",
                    str(REPO_ROOT),
                    "log",
                    "-n",
                    "1",
                    "--format=%H|%cd",
                    "--date=format-local:%Y-%m-%d",
                    ref,
                    "--",
                    pkg,
                ],
                text=True,
                env=git_env,
                stderr=subprocess.DEVNULL,
            ).strip()
            if "|" in out:
                sha, cdate = out.split("|", 1)
                if len(sha) == 40 and re.fullmatch(r"\d{4}-\d{2}-\d{2}", cdate):
                    return sha, cdate, f"{cdate}-{sha[:8]}"
        except Exception:
            pass

    # Fallback for untracked packages or non-git environments
    commit_date = time.strftime("%Y-%m-%d", time.gmtime())
    head_sha = ""
    for ref in valid_refs:
        try:
            out = subprocess.check_output(
                [
                    "git",
                    "--no-lazy-fetch",
                    "-C",
                    str(REPO_ROOT),
                    "show",
                    "-s",
                    "--format=%H|%cd",
                    "--date=format-local:%Y-%m-%d",
                    ref,
                ],
                text=True,
                env=git_env,
                stderr=subprocess.DEVNULL,
            ).strip()
            if "|" in out:
                sha, cdate = out.split("|", 1)
                if len(sha) == 40:
                    head_sha = sha
                if re.fullmatch(r"\d{4}-\d{2}-\d{2}", cdate):
                    commit_date = cdate
                break
        except Exception:
            pass

    raw_fb = fallback_commit.strip()
    pkg_commit = raw_fb if len(raw_fb) == 40 else (head_sha or raw_fb or "local")
    short_suffix = pkg_commit[:8] if len(pkg_commit) >= 8 and pkg_commit != "local" else state_sha256[:8]
    return pkg_commit, commit_date, f"{commit_date}-{short_suffix}"


def find_declaration_lines(lean_path: pathlib.Path, decl_names: list[str]) -> dict[str, int]:
    if not lean_path.is_file():
        return {}
    clean = strip_lean_comments(lean_path.read_text(encoding="utf-8", errors="replace"))
    lines = clean.splitlines()
    found: dict[str, int] = {}
    for full_name in decl_names:
        short = full_name.split(".")[-1]
        for candidate in (full_name, short):
            pat = re.compile(
                rf"^\s*(?:@\[[^\]]*\]\s*)*(?:private\s+|protected\s+|noncomputable\s+)*(?:theorem|lemma|def|abbrev)\s+{re.escape(candidate)}(?:[\s(:{{]|$)"
            )
            for idx, ln in enumerate(lines, start=1):
                if pat.match(ln):
                    found[full_name] = idx
                    break
            if full_name in found:
                break
    return found


def _strip_fc_source_for_inline(lean_txt: str, *, defs_only: bool = False) -> str:
    txt = re.sub(r"^module\s*\n", "", lean_txt, flags=re.M)
    txt = re.sub(r"/--[\s\S]*?-/", "", txt)
    txt = re.sub(r"^\s*(?:public\s+|private\s+)?(?:meta\s+)?import\s+.*?\n", "", txt, flags=re.M)
    txt = re.sub(r"@\[\s*category\b[\s\S]*?\]\s*\n", "", txt)
    txt = re.sub(r"(@\[[^\]]*\])\s*\n\s*", r"\1 ", txt)
    boundary_re = re.compile(
        r"^(?=\s*(?:@\[[^\]]*\]\s*)*(?:private\s|protected\s|noncomputable\s|theorem\s|lemma\s|proof_wanted\s|example\b|def\s|abbrev\s|structure\s|inductive\s|class\s|instance\b|namespace\s|section\b|end\b|open\s|variable\s|scoped\b|notation\b|#print\s))",
        re.M,
    )
    thm_head_re = re.compile(
        r"^\s*(?:@\[[^\]]*\]\s*)*(?:private\s+|protected\s+|noncomputable\s+)*(theorem|lemma|proof_wanted|example)\b"
    )
    chunks = boundary_re.split(txt)
    out_chunks: list[str] = []
    for ch in chunks:
        m_head = thm_head_re.match(ch)
        if m_head:
            kind = m_head.group(1)
            if defs_only and kind in ("proof_wanted", "example"):
                continue
            if kind in ("theorem", "lemma"):
                m_by = re.search(r":=\s*by\b", ch)
                if m_by:
                    ch = ch[: m_by.start()] + ":= by sorry\n"
                elif defs_only:
                    m_term = re.search(r":=", ch)
                    if m_term:
                        ch = ch[: m_term.start()] + ":= by sorry\n"
        elif defs_only and re.match(r"^\s*(?:@\[[^\]]*\]\s*)*(?:private\s+|protected\s+|noncomputable\s+)*(?:instance|def)\b", ch):
            ch = re.sub(r"(decode_encode\s+\S+\s*:=)\s*(?:by\b[\s\S]*|[^\n]+)", r"\1 by sorry", ch)
        out_chunks.append(ch)
    res_txt = "".join(out_chunks)
    return f"section\n{res_txt}\nend\n" if defs_only else res_txt


def _fetch_text_url(url: str) -> str | None:
    try:
        headers = {"User-Agent": "Mozilla/5.0"}
        gh_tok = os.environ.get("GITHUB_TOKEN", "").strip()
        if gh_tok and "github.com" in url:
            headers["Authorization"] = f"Bearer {gh_tok}"
        req = urllib.request.Request(url, headers=headers)
        with urllib.request.urlopen(req, timeout=10) as resp:
            return resp.read().decode("utf-8", errors="replace")
    except Exception:
        return None


def _drop_inline_declarations(snippet: str, short_names: list[str]) -> str:
    """Remove top-level theorem/lemma/def blocks whose short name is in short_names."""
    boundary_re = re.compile(
        r"^(?=\s*(?:@\[[^\]]*\]\s*)*(?:private\s|protected\s|noncomputable\s|theorem\s|lemma\s|example\b|def\s|abbrev\s|structure\s|inductive\s|class\s|instance\b|namespace\s|section\b|end\b|open\s|variable\s|scoped\b|notation\b|#print\s))",
        re.M,
    )
    names = "|".join(re.escape(n) for n in short_names)
    head_re = re.compile(
        rf"^\s*(?:@\[[^\]]*\]\s*)*(?:private\s+|protected\s+|noncomputable\s+)*(?:theorem|lemma|def|abbrev)\s+(?:{names})\b"
    )
    return "".join(ch for ch in boundary_re.split(snippet) if not head_re.match(ch))


def fetch_and_compile_fc_problem_olean(
    pkg: str,
    prob: str,
    pkg_dir: pathlib.Path,
    out_olean: pathlib.Path,
) -> pathlib.Path | None:
    fc_ref = "main"
    fy_path = pkg_dir / "formalization.yaml"
    if fy_path.is_file():
        try:
            fy = json.loads(fy_path.read_text(encoding="utf-8"))
            for src in fy.get("sources", []) + fy.get("related_formalizations", []):
                sid = str(src.get("id", ""))
                m_ref = re.search(
                    r"github\.com/google-deepmind/formal-conjectures/(?:blob|tree)/([^/]+)/FormalConjectures",
                    sid,
                )
                if m_ref:
                    fc_ref = m_ref.group(1)
                    break
        except Exception:
            pass

    fc_git_env = os.environ.get("FC_GIT_DIR", "").strip()
    local_fc_root = pathlib.Path(fc_git_env).resolve() if fc_git_env else (REPO_ROOT.parent / "formal-conjectures")
    local_prob_file = local_fc_root / "FormalConjectures" / "ErdosProblems" / f"{prob}.lean"
    prob_raw: str | None = None
    if local_prob_file.is_file():
        prob_raw = local_prob_file.read_text(encoding="utf-8", errors="replace")
    elif (local_fc_root / ".git").is_dir():
        for git_ref in (f"erdos-{prob}", fc_ref, "origin/main", "main"):
            try:
                prob_raw = subprocess.check_output(
                    ["git", "-C", str(local_fc_root), "show", f"{git_ref}:FormalConjectures/ErdosProblems/{prob}.lean"],
                    text=True,
                    stderr=subprocess.DEVNULL,
                )
                if prob_raw:
                    break
            except Exception:
                pass
    if not prob_raw:
        for ref in ([fc_ref, "main"] if fc_ref != "main" else ["main"]):
            url = f"https://raw.githubusercontent.com/google-deepmind/formal-conjectures/{ref}/FormalConjectures/ErdosProblems/{prob}.lean"
            prob_raw = _fetch_text_url(url)
            if prob_raw:
                fc_ref = ref
                break
        if not prob_raw:
            for fork_owner in ("google-deepmind", "linrock"):
                url = f"https://raw.githubusercontent.com/{fork_owner}/formal-conjectures/erdos-{prob}/FormalConjectures/ErdosProblems/{prob}.lean"
                prob_raw = _fetch_text_url(url)
                if prob_raw:
                    break

    if not prob_raw:
        return None

    elan_lean = pathlib.Path.home() / ".elan" / "toolchains" / "leanprover--lean4---v4.35.0-rc2" / "bin" / "lean"
    lean_bin = str(elan_lean) if elan_lean.is_file() else "lean"
    try:
        lp = subprocess.check_output(
            ["lake", "env", "printenv", "LEAN_PATH"],
            cwd=pkg_dir,
            text=True,
            stderr=subprocess.DEVNULL,
        ).strip()
    except Exception:
        return None

    prob_body = _strip_fc_source_for_inline(prob_raw, defs_only=False)
    helper_snippets: list[str] = []
    loaded_helper_rels: set[str] = set()
    remote_fc_tree: list[str] | None = None

    def resolve_missing_helpers(identifiers: list[str]) -> bool:
        nonlocal remote_fc_tree
        ignored_mathlib_ids = {"log", "atTop", "atBot", "nhds", "Icc", "Ico", "Ioc", "Ioo", "Ici", "Ioi", "Iic", "Iio"}
        identifiers = [i for i in identifiers if i.split(".")[-1] not in ignored_mathlib_ids]
        if not identifiers:
            return False
        added_any = False
        fc_mathlib_dir = local_fc_root / "FormalConjecturesForMathlib"
        if fc_mathlib_dir.is_dir():
            def add_local_helper_rel(rel: str) -> None:
                nonlocal added_any
                if rel in loaded_helper_rels:
                    return
                hp = local_fc_root / rel
                if not hp.is_file():
                    return
                loaded_helper_rels.add(rel)
                htxt = hp.read_text(encoding="utf-8", errors="replace")
                for m_imp in re.finditer(r"import\s+(FormalConjecturesForMathlib\.[\w.]+)", htxt):
                    imp_rel = m_imp.group(1).replace(".", "/") + ".lean"
                    add_local_helper_rel(imp_rel)
                helper_snippets.append(_strip_fc_source_for_inline(htxt, defs_only=True))
                added_any = True

            for ident in identifiers:
                short_id = ident.split(".")[-1]
                pat = re.compile(
                    rf"\b(?:def|abbrev|structure|inductive|class|notation|scoped|namespace)\b[^\n]*\b{re.escape(short_id)}\b"
                )
                for p in sorted(fc_mathlib_dir.rglob("*.lean")):
                    rel = p.relative_to(local_fc_root).as_posix()
                    if rel in loaded_helper_rels:
                        continue
                    txt = p.read_text(encoding="utf-8", errors="replace")
                    if pat.search(txt):
                        add_local_helper_rel(rel)
            return added_any

        if remote_fc_tree is None:
            tree_txt = _fetch_text_url(
                f"https://api.github.com/repos/google-deepmind/formal-conjectures/git/trees/{fc_ref}?recursive=1"
            )
            if tree_txt:
                try:
                    tree_data = json.loads(tree_txt)
                    remote_fc_tree = [
                        item["path"]
                        for item in tree_data.get("tree", [])
                        if str(item.get("path", "")).startswith("FormalConjecturesForMathlib/")
                        and str(item.get("path", "")).endswith(".lean")
                    ]
                except Exception:
                    remote_fc_tree = []
            else:
                remote_fc_tree = []

        for ident in identifiers:
            short_id = ident.split(".")[-1]
            pat = re.compile(
                rf"\b(?:def|abbrev|structure|inductive|class|notation|scoped|namespace)\b[^\n]*\b{re.escape(short_id)}\b"
            )
            def add_remote_helper_rel(rel: str) -> None:
                nonlocal added_any
                if rel in loaded_helper_rels:
                    return
                rtxt = _fetch_text_url(
                    f"https://raw.githubusercontent.com/google-deepmind/formal-conjectures/{fc_ref}/{rel}"
                )
                if not rtxt:
                    return
                loaded_helper_rels.add(rel)
                for m_imp in re.finditer(r"import\s+(FormalConjecturesForMathlib\.[\w.]+)", rtxt):
                    imp_rel = m_imp.group(1).replace(".", "/") + ".lean"
                    add_remote_helper_rel(imp_rel)
                helper_snippets.append(_strip_fc_source_for_inline(rtxt, defs_only=True))
                added_any = True

            for rel in remote_fc_tree or []:
                if rel in loaded_helper_rels:
                    continue
                txt = _fetch_text_url(
                    f"https://raw.githubusercontent.com/google-deepmind/formal-conjectures/{fc_ref}/{rel}"
                )
                if txt and pat.search(txt):
                    add_remote_helper_rel(rel)
        return added_any

    with tempfile.TemporaryDirectory(prefix=f"fc_on_demand_{prob}_") as tmp_str:
        tdir = pathlib.Path(tmp_str)
        src_file = tdir / f"Prob{prob}.lean"
        env = os.environ.copy()
        env["LEAN_PATH"] = f"{tdir}:{lp}"
        for _attempt in range(6):
            combined = FC_UTIL_SHIM_HEADER + "\n" + "\n".join(helper_snippets) + "\n" + prob_body
            src_file.write_text(combined, encoding="utf-8")
            res = subprocess.run(
                [lean_bin, "-M", "8192", "-j4", "-Dlinter.deprecated=false", "-R", str(tdir), str(src_file), "-o", str(out_olean)],
                cwd=pkg_dir,
                env=env,
                capture_output=True,
                text=True,
            )
            if res.returncode == 0 and out_olean.is_file():
                return out_olean
            err_out = (res.stdout or "") + "\n" + (res.stderr or "")
            dup_names = re.findall(r"[`']([^`'\s]+)[`'] has already been declared", err_out)
            if dup_names:
                helper_snippets[:] = [
                    _drop_inline_declarations(snip, [n.split(".")[-1] for n in dup_names])
                    for snip in helper_snippets
                ]
                continue
            missing_ids = re.findall(
                r"(?:Unknown identifier|Invalid field|unknown constant|unknown namespace|The identifier)\s+[`']([^`'\s]+)[`']",
                err_out,
                re.IGNORECASE,
            )
            if not missing_ids or not resolve_missing_helpers(sorted(set(missing_ids))):
                break
    return None


def summarize_package(
    pkg: str,
    commit: str,
    repo: str,
    run_id: str,
    step_summary: str | None,
    *,
    require_comparator: bool = False,
    require_sandbox: bool = False,
    step_failed: bool = False,
) -> int:
    pkg_dir = REPO_ROOT / pkg
    ver_dir = pkg_dir / ".verification"
    comp = json.loads((pkg_dir / "comparator.json").read_text(encoding="utf-8"))
    fy = json.loads((pkg_dir / "formalization.yaml").read_text(encoding="utf-8"))
    comp_theorems: list[str] = comp.get("theorem_names", [])
    aud_path = pkg_dir / "AxiomAudit.lean"
    expected_axiom_reports = (
        len(
            re.findall(
                r"^[ \t]*#print[ \t]+axioms[ \t]+[^\s]+",
                strip_lean_comments(aud_path.read_text(encoding="utf-8", errors="replace")),
                re.M,
            )
        )
        if aud_path.is_file()
        else len(comp_theorems)
    )

    toolchain_txt = (
        (ver_dir / "toolchain.log").read_text(encoding="utf-8").strip()
        if (ver_dir / "toolchain.log").is_file()
        else EXPECTED_TOOLCHAIN
    )
    axiom_pairs = parse_axioms_log(ver_dir / "axioms.log")
    axiom_map = dict(axiom_pairs)

    env_log = (
        (ver_dir / "env_compare.log").read_text(encoding="utf-8", errors="replace")
        if (ver_dir / "env_compare.log").is_file()
        else ""
    )
    env_matched = {
        line.removeprefix("ENV_MATCH ").strip()
        for line in env_log.splitlines()
        if line.startswith("ENV_MATCH ")
    }

    comp_log = (
        (ver_dir / "comparator.log").read_text(encoding="utf-8", errors="replace")
        if (ver_dir / "comparator.log").is_file()
        else ""
    )
    nanoda_ok = "nanoda kernel accepts the solution" in comp_log
    con_ron_ok = "con-ron kernel accepts the solution" in comp_log
    lean_kernel_ok = "Lean default kernel accepts the solution" in comp_log
    solution_ok = "Your solution is okay!" in comp_log
    sandbox_enabled = bool(comp_log) and ("WARNING: Sandbox disabled" not in comp_log)

    core_audit_rows: list[dict[str, str]] = []
    if (ver_dir / "core_notation_audit.json").is_file():
        try:
            core_audit_rows = json.loads(
                (ver_dir / "core_notation_audit.json").read_text(encoding="utf-8")
            )
        except Exception:
            core_audit_rows = []

    fc_audit_rows: list[dict[str, str]] = []
    if (ver_dir / "fc_statement_audit.json").is_file():
        try:
            fc_audit_rows = json.loads(
                (ver_dir / "fc_statement_audit.json").read_text(encoding="utf-8")
            )
        except Exception:
            fc_audit_rows = []

    resource_usage: dict[str, Any] = {}
    if (ver_dir / "resource_usage.json").is_file():
        try:
            resource_usage = json.loads(
                (ver_dir / "resource_usage.json").read_text(encoding="utf-8")
            )
        except Exception:
            resource_usage = {}

    chal_path = pkg_dir / "Challenge.lean"
    chal_bytes = chal_path.stat().st_size if chal_path.is_file() else 0
    chal_lines = len(chal_path.read_text(encoding="utf-8", errors="replace").splitlines()) if chal_path.is_file() else 0

    bad_axioms = [
        (decl, axs)
        for decl, axs in axiom_pairs
        if any(a not in PERMITTED_AXIOMS for a in axs)
    ]
    missing_from_axioms = [t for t in comp_theorems if t not in axiom_map]
    missing_from_env = [t for t in comp_theorems if t not in env_matched]
    fc_matched = {
        str(row.get("solution_declaration", ""))
        for row in fc_audit_rows
        if row.get("status") == "PASS"
    }
    direct_fc_sol = any(
        row.get("status") == "PASS"
        and str(row.get("source", "")).startswith("FormalConjectures.ErdosProblems.")
        for row in fc_audit_rows
    )
    if direct_fc_sol or any(row.get("status") == "PASS" for row in fc_audit_rows):
        missing_from_fc = []
    else:
        missing_from_fc = [t for t in comp_theorems if t not in fc_matched]
    sandbox_ok = sandbox_enabled if require_sandbox else True
    comparator_ok = (
        (bool(comp_log) and nanoda_ok and con_ron_ok and lean_kernel_ok and solution_ok and sandbox_ok)
        if require_comparator
        else ((not comp_log) or (nanoda_ok and con_ron_ok and lean_kernel_ok and solution_ok))
    )

    status = (
        "PASS"
        if (
            not step_failed
            and axiom_pairs
            and len(axiom_pairs) == expected_axiom_reports
            and not bad_axioms
            and not missing_from_axioms
            and not missing_from_env
            and not missing_from_fc
            and bool(core_audit_rows)
            and comparator_ok
        )
        else "FAIL"
    )

    input_sha256 = collect_input_sha256(pkg_dir)
    state_sha256 = compute_package_state_sha256(pkg, input_sha256)
    pkg_commit, commit_date, verification_id = resolve_package_commit_and_id(
        pkg, commit, state_sha256
    )
    sol_lines_map = find_declaration_lines(pkg_dir / "Solution.lean", comp_theorems)
    chal_lines_map = find_declaration_lines(pkg_dir / "Challenge.lean", comp_theorems)

    receipt: dict[str, Any] = {
        "schema_version": 2,
        "verification_id": verification_id,
        "verification_date": commit_date,
        "state_sha256": state_sha256,
        "package": pkg,
        "project_name": fy.get("project", {}).get("name", pkg),
        "package_commit": pkg_commit,
        "commit": commit,
        "repository": repo,
        "run_id": run_id,
        "lean_toolchain": toolchain_txt,
        "mathlib_revision": EXPECTED_MATHLIB_REV,
        "challenge": {
            "path": "Challenge.lean",
            "bytes": chal_bytes,
            "lines": chal_lines,
            "sha256": sha256_file(chal_path) if chal_path.is_file() else "",
            "trust_level": "high",
        },
        "exported_theorems": comp_theorems,
        "declaration_lines": {
            thm: {
                "solution_line": sol_lines_map.get(thm),
                "challenge_line": chal_lines_map.get(thm),
            }
            for thm in comp_theorems
        },
        "env_comparison_matched": sorted(env_matched),
        "missing_from_axioms_log": missing_from_axioms,
        "missing_from_env_compare": missing_from_env,
        "missing_from_fc_statement_audit": missing_from_fc,
        "axiom_audit_count": len(axiom_pairs),
        "expected_axiom_audit_count": expected_axiom_reports,
        "axiom_reports": [
            {"declaration": decl, "axioms": axs} for decl, axs in axiom_pairs
        ],
        "core_notation_audit": core_audit_rows,
        "fc_statement_audit": fc_audit_rows,
        "comparator_required": require_comparator,
        "comparator_ran": bool(comp_log),
        "sandbox_enabled": sandbox_enabled,
        "kernels": {
            "nanoda_accepted": nanoda_ok,
            "con_ron_accepted": con_ron_ok,
            "lean_kernel_accepted": lean_kernel_ok,
        },
        "nanoda_accepted": nanoda_ok,
        "con_ron_accepted": con_ron_ok,
        "lean_kernel_accepted": lean_kernel_ok,
        "tool_digests": collect_tool_digests(pkg_dir),
        "input_sha256": input_sha256,
        "resource_usage": resource_usage,
        "status": status,
    }
    ver_dir.mkdir(parents=True, exist_ok=True)
    (ver_dir / "VERIFICATION.json").write_text(
        json.dumps(receipt, indent=2) + "\n", encoding="utf-8"
    )

    link_commit = pkg_commit if len(pkg_commit) == 40 else (commit if len(commit) == 40 else "")
    md_lines = [
        f"## `{pkg}` Verification Summary ({status})",
        "",
        f"- **Verification ID:** `{verification_id}` (`state_sha256={state_sha256[:16]}...`)",
        f"- **Project:** {fy.get('project', {}).get('name', pkg)}",
        f"- **Package commit:** `{pkg_commit}`" + (f" ([tree](https://github.com/{repo}/tree/{link_commit}/{pkg}))" if repo and link_commit else ""),
        f"- **Compiler:** `{toolchain_txt}`",
        f"- **Mathlib:** `{EXPECTED_MATHLIB_REV}`",
        f"- **Challenge surface:** `{chal_lines}` lines, `{chal_bytes}` bytes (`trust_level=high`)",
        f"- **Challenge ↔ Solution environment match:** `{len(env_matched)}/{len(comp_theorems)}` theorems",
        f"- **Endpoint `#print axioms` checks:** `{len(axiom_pairs)}/{expected_axiom_reports}` (permitted: `propext`, `Classical.choice`, `Quot.sound`)",
    ]
    if fc_audit_rows:
        md_lines.append(
            f"- **Formal Conjectures / Statement matches:** `{len(fc_audit_rows)}` verified statement equivalence(s)"
        )
    if comp_log or require_comparator:
        md_lines.append(
            f"- **Comparator (3 kernels):** NanoDa=`{nanoda_ok}`, con-ron=`{con_ron_ok}`, Lean default kernel=`{lean_kernel_ok}` (bwrap sandbox=`{sandbox_enabled}`)"
        )
    if resource_usage:
        md_lines.append(
            f"- **Resource usage:** total=`{resource_usage.get('total_elapsed_seconds', 0):.1f}s`, peak RSS=`{resource_usage.get('peak_rss_mib', 0):.1f} MiB`"
        )
    if bad_axioms:
        md_lines.append(f"- **DISALLOWED axioms:** `{bad_axioms}`")
    if missing_from_axioms:
        md_lines.append(f"- **MISSING from `axioms.log`:** `{missing_from_axioms}`")
    if missing_from_env:
        md_lines.append(f"- **MISSING from `Challenge`/`Solution` match:** `{missing_from_env}`")
    if missing_from_fc:
        md_lines.append(f"- **MISSING from upstream statement audit:** `{missing_from_fc}`")
    md_lines.extend([
        "",
        "### Exported Theorems & Axiom Footprint",
        "",
        "| Declaration | Source Links | Challenge = Solution | Axioms |",
        "| --- | --- | --- | --- |",
    ])
    for thm in comp_theorems:
        axs = axiom_map.get(thm)
        axs_str = (
            ", ".join(f"`{a}`" for a in axs)
            if axs
            else ("`none`" if axs == [] else "**MISSING**")
        )
        matched_str = "PASS" if thm in env_matched else "**FAIL**"
        s_line = sol_lines_map.get(thm)
        c_line = chal_lines_map.get(thm)
        links_parts: list[str] = []
        if s_line:
            if repo and link_commit:
                links_parts.append(
                    f"[`Solution.lean#L{s_line}`](https://github.com/{repo}/blob/{link_commit}/{pkg}/Solution.lean#L{s_line})"
                )
            else:
                links_parts.append(f"`Solution.lean#L{s_line}`")
        if c_line:
            if repo and link_commit:
                links_parts.append(
                    f"[`Challenge.lean#L{c_line}`](https://github.com/{repo}/blob/{link_commit}/{pkg}/Challenge.lean#L{c_line})"
                )
            else:
                links_parts.append(f"`Challenge.lean#L{c_line}`")
        links_cell = ", ".join(links_parts) if links_parts else "-"
        md_lines.append(f"| `{thm}` | {links_cell} | {matched_str} | {axs_str} |")

    if fc_audit_rows:
        md_lines.extend([
            "",
            "### Statement-Equivalence Audit (`FCCompare`)",
            "",
            "| Source | Target Declaration | Solution Declaration | Match Mode | Status |",
            "| --- | --- | --- | --- | --- |",
        ])
        for row in fc_audit_rows:
            md_lines.append(
                f"| `{row.get('source', '')}` | `{row.get('target_declaration', '')}` | "
                f"`{row.get('solution_declaration', '')}` | `{row.get('match_mode', '')}` | "
                f"{row.get('status', 'PASS')} |"
            )

    clean_axiom_lines = [
        f"'{decl}' depends on axioms: [{', '.join(axs)}]"
        if axs
        else f"'{decl}' does not depend on any axioms"
        for decl, axs in axiom_pairs
    ]
    clean_comp_lines = [
        ln.strip()
        for ln in comp_log.splitlines()
        if any(
            k in ln
            for k in (
                "kernel accepts the solution",
                "Your solution is okay!",
                "Sandbox",
                "Checking",
            )
        )
    ]
    if clean_axiom_lines or clean_comp_lines:
        md_lines.extend([
            "",
            "<details>",
            "<summary>Axiom & Multi-Kernel Verification Logs (<code>axioms.log</code>, <code>comparator.log</code>)</summary>",
            "",
            "```text",
        ])
        if clean_axiom_lines:
            md_lines.append("=== axioms.log ===")
            md_lines.extend(clean_axiom_lines)
        if clean_comp_lines:
            md_lines.append("=== comparator.log ===")
            md_lines.extend(clean_comp_lines)
        md_lines.extend([
            "```",
            "</details>",
        ])

    if core_audit_rows:
        md_lines.extend([
            "",
            "<details>",
            "<summary>Core-Notation Statement Audit (<code>loadExts := false</code>, <code>pp.notation := false</code>)</summary>",
            "",
            "```lean",
        ])
        for row in core_audit_rows:
            md_lines.append(row.get("declaration", ""))
        md_lines.extend([
            "```",
            "</details>",
        ])

    summary_md = "\n".join(md_lines) + "\n"
    (ver_dir / "VERIFICATION.md").write_text(summary_md, encoding="utf-8")
    print(summary_md)
    if step_summary:
        with open(step_summary, "a", encoding="utf-8") as f:
            f.write(summary_md)

    return 0 if status == "PASS" else 1


def run_fc_statement_comparison(
    pkg: str,
    *,
    fc_lib_dir: str | None = None,
    fc_olean: str | None = None,
    sol_olean: str | None = None,
    pairs: list[str] | None = None,
    out_json: str | None = None,
    strict: bool = False,
) -> int:
    pkg_dir = REPO_ROOT / pkg if pkg else REPO_ROOT
    ver_dir = pkg_dir / ".verification" if pkg else REPO_ROOT / ".verification"
    ver_dir.mkdir(parents=True, exist_ok=True)

    olean_dir = pkg_dir / ".lake" / "build" / "lib" / "lean"
    sol_olean_path = pathlib.Path(sol_olean).resolve() if sol_olean else (olean_dir / "Solution.olean")
    if not sol_olean_path.is_file():
        sys.stderr.write(f"fc-compare: missing Solution.olean at {sol_olean_path}\n")
        return 1

    comp_theorems: list[str] = []
    if (pkg_dir / "comparator.json").is_file():
        try:
            comp = json.loads((pkg_dir / "comparator.json").read_text(encoding="utf-8"))
            comp_theorems = comp.get("theorem_names", [])
        except Exception:
            comp_theorems = []

    resolved_fc_lib = fc_lib_dir or os.environ.get("FC_LEAN_LIB_DIR", "")
    targets: list[tuple[str, pathlib.Path, str]] = []
    temp_fc_olean: pathlib.Path | None = None
    if fc_olean:
        fc_p = pathlib.Path(fc_olean).resolve()
        if not fc_p.is_file():
            sys.stderr.write(f"fc-compare: missing target olean {fc_p}\n")
            return 1
        prob_m = re.match(r"^erdos-(\d+)$", pkg)
        label = f"FormalConjectures.ErdosProblems.{prob_m.group(1)}" if prob_m else fc_p.stem
        targets.append(("pairs" if pairs else "discover", fc_p, label))
    else:
        prob_m = re.match(r"^erdos-(\d+)$", pkg)
        added_fc = False
        if prob_m and resolved_fc_lib:
            cand_fc = pathlib.Path(resolved_fc_lib).resolve() / "FormalConjectures" / "ErdosProblems" / f"{prob_m.group(1)}.olean"
            if cand_fc.is_file():
                targets.append(("pairs" if pairs else "discover", cand_fc, f"FormalConjectures.ErdosProblems.{prob_m.group(1)}"))
                added_fc = True
        if prob_m and not added_fc:
            on_demand_olean = ver_dir / f"FCProb{prob_m.group(1)}.olean"
            compiled_fc = fetch_and_compile_fc_problem_olean(pkg, prob_m.group(1), pkg_dir, on_demand_olean)
            if compiled_fc and compiled_fc.is_file():
                if resolved_fc_lib:
                    try:
                        dest_fc = pathlib.Path(resolved_fc_lib).resolve() / "FormalConjectures" / "ErdosProblems" / f"{prob_m.group(1)}.olean"
                        dest_fc.parent.mkdir(parents=True, exist_ok=True)
                        shutil.copy2(compiled_fc, dest_fc)
                        compiled_fc.unlink(missing_ok=True)
                        targets.append(("pairs" if pairs else "discover", dest_fc, f"FormalConjectures.ErdosProblems.{prob_m.group(1)}"))
                    except Exception:
                        temp_fc_olean = compiled_fc
                        targets.append(("pairs" if pairs else "discover", compiled_fc, f"FormalConjectures.ErdosProblems.{prob_m.group(1)}"))
                else:
                    temp_fc_olean = compiled_fc
                    targets.append(("pairs" if pairs else "discover", compiled_fc, f"FormalConjectures.ErdosProblems.{prob_m.group(1)}"))
                added_fc = True
        stmt_olean = olean_dir / "Statement.olean"
        if not pairs and stmt_olean.is_file():
            targets.append(("discover", stmt_olean.resolve(), "Statement"))
        fc_git_env = os.environ.get("FC_GIT_DIR", "").strip()
        fc_root_check = pathlib.Path(fc_git_env).resolve() if fc_git_env else (REPO_ROOT.parent / "formal-conjectures")
        local_fc_prob = (
            fc_root_check / "FormalConjectures" / "ErdosProblems" / f"{prob_m.group(1)}.lean"
            if prob_m
            else None
        )
        if prob_m and not added_fc and not pairs and strict and (not stmt_olean.is_file() or (local_fc_prob and local_fc_prob.is_file())):
            sys.stderr.write(
                f"fc-compare: strict mode requires a direct FormalConjectures.ErdosProblems.{prob_m.group(1)} target for {pkg}\n"
            )
            return 1

    if not targets:
        if strict:
            if prob_m:
                sys.stderr.write(
                    f"fc-compare: no FormalConjectures.ErdosProblems.{prob_m.group(1)} target found for {pkg}\n"
                )
            else:
                sys.stderr.write(f"fc-compare: no upstream target found for {pkg}\n")
            return 1
        return 0

    audit_json_path = pathlib.Path(out_json).resolve() if out_json else (ver_dir / "fc_statement_audit.json")
    if audit_json_path.exists():
        audit_json_path.unlink()

    fc_compare_file = ver_dir / "FCCompare.lean"
    fc_compare_file.write_text(FC_COMPARE_LEAN, encoding="utf-8")
    env_run = os.environ.copy()
    extra_paths: list[str] = [str(sol_olean_path.parent)]
    if olean_dir.is_dir():
        extra_paths.append(str(olean_dir.resolve()))
    if resolved_fc_lib and pathlib.Path(resolved_fc_lib).is_dir():
        extra_paths.append(str(pathlib.Path(resolved_fc_lib).resolve()))
    existing_lp = env_run.get("LEAN_PATH", "")
    env_run["LEAN_PATH"] = ":".join(extra_paths + ([existing_lp] if existing_lp else []))

    lean_cmd_prefix = ["lake", "env", "lean", "--run"]
    elan_lean = pathlib.Path.home() / ".elan" / "toolchains" / "leanprover--lean4---v4.35.0-rc2" / "bin" / "lean"
    if elan_lean.is_file():
        lean_cmd_prefix = [str(elan_lean), "--run"]

    rc = 0
    matched_declarations: set[str] = set()
    fc_stmt_bridge_json = ver_dir / "fc_stmt_bridge_audit.json"
    if fc_stmt_bridge_json.exists():
        fc_stmt_bridge_json.unlink()
    try:
        with open(ver_dir / "fc_compare.log", "w", encoding="utf-8") as lf:
            for mode, target_p, source_label in targets:
                tail_args = list(pairs) if (mode == "pairs" and pairs) else comp_theorems
                cmd = lean_cmd_prefix + [
                    str(fc_compare_file.resolve()),
                    mode,
                    str(target_p),
                    str(sol_olean_path),
                    source_label,
                    str(audit_json_path),
                ] + tail_args
                res = subprocess.run(
                    cmd,
                    cwd=pkg_dir if pkg_dir.is_dir() else REPO_ROOT,
                    env=env_run,
                    stdout=lf,
                    stderr=subprocess.STDOUT,
                )
                if res.returncode != 0:
                    rc = res.returncode
            stmt_olean_check = olean_dir / "Statement.olean"
            fc_targets = [
                (tp, sl) for m, tp, sl in targets
                if m == "discover" and sl.startswith("FormalConjectures.ErdosProblems.")
            ]
            if rc == 0 and not pairs and fc_targets and stmt_olean_check.is_file():
                fc_tp, fc_sl = fc_targets[0]
                cmd_bridge = lean_cmd_prefix + [
                    str(fc_compare_file.resolve()),
                    "discover",
                    str(fc_tp),
                    str(stmt_olean_check.resolve()),
                    fc_sl,
                    str(fc_stmt_bridge_json.resolve()),
                ]
                res_b = subprocess.run(
                    cmd_bridge,
                    cwd=pkg_dir if pkg_dir.is_dir() else REPO_ROOT,
                    env=env_run,
                    stdout=lf,
                    stderr=subprocess.STDOUT,
                )
                if res_b.returncode != 0:
                    rc = res_b.returncode
                elif fc_stmt_bridge_json.is_file():
                    try:
                        audit_rows = (
                            json.loads(audit_json_path.read_text(encoding="utf-8"))
                            if audit_json_path.is_file()
                            else []
                        )
                        bridge_rows = json.loads(
                            fc_stmt_bridge_json.read_text(encoding="utf-8")
                        )
                        existing_rows = {
                            json.dumps(row, sort_keys=True, separators=(",", ":"))
                            for row in audit_rows
                        }
                        for row in bridge_rows:
                            row_key = json.dumps(
                                row, sort_keys=True, separators=(",", ":")
                            )
                            if row_key not in existing_rows:
                                audit_rows.append(row)
                                existing_rows.add(row_key)
                        audit_json_path.write_text(
                            json.dumps(audit_rows, indent=2) + "\n",
                            encoding="utf-8",
                        )
                    except Exception as exc:
                        rc = 1
                        print(
                            f"fc-compare: could not persist Statement bridge audit for {pkg}: {exc}",
                            file=lf,
                        )
        if rc == 0 and strict:
            try:
                audit_rows = json.loads(audit_json_path.read_text(encoding="utf-8"))
                matched_declarations = {
                    str(row.get("solution_declaration", ""))
                    for row in audit_rows
                    if row.get("status") == "PASS"
                }
                has_fc_target = any(
                    sl.startswith("FormalConjectures.ErdosProblems.")
                    for _, _, sl in targets
                )
                direct_fc_sol = any(
                    row.get("status") == "PASS"
                    and str(row.get("source", "")).startswith("FormalConjectures.ErdosProblems.")
                    for row in audit_rows
                )
                direct_fc_stmt = False
                if fc_stmt_bridge_json.is_file():
                    try:
                        bridge_rows = json.loads(fc_stmt_bridge_json.read_text(encoding="utf-8"))
                        direct_fc_stmt = any(
                            r.get("status") == "PASS" for r in bridge_rows
                        )
                    except Exception:
                        direct_fc_stmt = False
                if has_fc_target and not pairs and not (direct_fc_sol or direct_fc_stmt):
                    rc = 1
                    sys.stderr.write(
                        f"fc-compare: no declaration in Solution or Statement matched upstream FormalConjectures target for {pkg}\n"
                    )
                elif not (direct_fc_sol or direct_fc_stmt or matched_declarations):
                    missing_matches = [
                        theorem
                        for theorem in comp_theorems
                        if theorem not in matched_declarations
                    ]
                    if missing_matches:
                        rc = 1
                        sys.stderr.write(
                            "fc-compare: missing upstream statement matches for "
                            f"{pkg}: {missing_matches}\n"
                        )
            except Exception as exc:
                rc = 1
                sys.stderr.write(f"fc-compare: invalid FC audit JSON for {pkg}: {exc}\n")
        if rc != 0:
            sys.stderr.write((ver_dir / "fc_compare.log").read_text(encoding="utf-8", errors="replace"))
    finally:
        fc_compare_file.unlink(missing_ok=True)
        fc_stmt_bridge_json.unlink(missing_ok=True)
        if temp_fc_olean is not None:
            temp_fc_olean.unlink(missing_ok=True)
    return rc


def run_package_verification(
    pkg: str,
    shared_packages: str | None,
    run_comparator: bool,
    commit: str,
    repo: str,
    run_id: str,
    step_summary: str | None,
    *,
    force_no_sandbox: bool = False,
    fc_lib_dir: str | None = None,
) -> int:
    pkg_dir = REPO_ROOT / pkg
    ver_dir = pkg_dir / ".verification"
    ver_dir.mkdir(parents=True, exist_ok=True)
    for stale in (
        "toolchain.log",
        "build.log",
        "axioms.log",
        "comparator.log",
        "env_compare.log",
        "fc_compare.log",
        "core_notation_audit.json",
        "fc_statement_audit.json",
        "resource_usage.json",
        "comparator.protected.json",
        "VERIFICATION.json",
        "VERIFICATION.md",
    ):
        stale_path = ver_dir / stale
        if stale_path.exists():
            stale_path.unlink()

    t_start = time.time()
    step_failed = False
    verify_sh_sec = 0.0
    env_cmp_sec = 0.0
    try:
        lake_pkgs = pkg_dir / ".lake" / "packages"
        if shared_packages and pathlib.Path(shared_packages).is_dir():
            shared_path = pathlib.Path(shared_packages).resolve()
            lake_pkgs.parent.mkdir(parents=True, exist_ok=True)
            if lake_pkgs.is_symlink() and not lake_pkgs.exists():
                lake_pkgs.unlink()
            if not lake_pkgs.exists():
                os.symlink(shared_path, lake_pkgs)
        if not (lake_pkgs / "mathlib" / ".lake" / "build" / "lib" / "lean" / "Mathlib.olean").is_file():
            res_cache = subprocess.run(["lake", "exe", "cache", "get"], cwd=pkg_dir)
            if res_cache.returncode != 0:
                step_failed = True

        verify_sh = pkg_dir / "verify.sh"
        t_verify_sh = time.time()
        if not step_failed and verify_sh.is_file():
            res_v = subprocess.run(["./verify.sh"], cwd=pkg_dir)
            if res_v.returncode != 0:
                step_failed = True
                for log_name in ("build.log", "axioms.log", "comparator.log"):
                    log_path = ver_dir / log_name
                    if log_path.is_file():
                        sys.stderr.write(f"--- {log_name} ---\n")
                        sys.stderr.write(log_path.read_text(encoding="utf-8", errors="replace"))
        elif not step_failed:
            sys.stderr.write(f"{pkg}: missing verify.sh\n")
            step_failed = True
        verify_sh_sec = round(time.time() - t_verify_sh, 3)

        if not step_failed and run_comparator:
            try:
                lean_prefix_str = subprocess.check_output(
                    ["lake", "env", "lean", "--print-prefix"],
                    cwd=pkg_dir,
                    text=True,
                    stderr=subprocess.DEVNULL,
                ).strip()
                lean_prefix = pathlib.Path(lean_prefix_str).resolve()
                comp_cfg = json.loads((pkg_dir / "comparator.json").read_text(encoding="utf-8"))
                prot_cfg = dict(comp_cfg)
                prot_cfg.pop("enable_nanoda", None)
                prot_cfg["external_kernels"] = {
                    "nanoda": [str(lean_prefix / "bin" / "nanoda_bin")],
                    "con-ron": [str(lean_prefix / "bin" / "con-ron"), "--jobs=2"],
                }
                prot_cfg_path = ver_dir / "comparator.protected.json"
                prot_cfg_path.write_text(json.dumps(prot_cfg, indent=2) + "\n", encoding="utf-8")
                bwrap_ok = (
                    not force_no_sandbox
                    and not (pkg_dir / ".lake" / "packages").is_symlink()
                    and shutil.which("bwrap") is not None
                    and subprocess.run(
                        [
                            "env", "-i", "bwrap", "--ro-bind", "/", "/", "--dev", "/dev",
                            "--proc", "/proc", "--clearenv", "--tmpfs", "/run", "--tmpfs", "/var",
                            "--unshare-all", "--die-with-parent", "--new-session", "--", "/bin/true",
                        ],
                        stdout=subprocess.DEVNULL,
                        stderr=subprocess.DEVNULL,
                    ).returncode == 0
                )
                comp_cmd = [
                    "lake", "env", "lake", "comparator",
                    "--config", ".verification/comparator.protected.json",
                ]
                if not bwrap_ok:
                    comp_cmd.append("--inadvisably-no-sandbox")
                env_comp = os.environ.copy()
                env_comp["LEAN_ABORT_ON_PANIC"] = "1"
                with open(ver_dir / "comparator.log", "w", encoding="utf-8") as clf:
                    res_c = subprocess.run(comp_cmd, cwd=pkg_dir, env=env_comp, stdout=clf, stderr=subprocess.STDOUT)
                sys.stdout.write((ver_dir / "comparator.log").read_text(encoding="utf-8", errors="replace"))
                if res_c.returncode != 0:
                    step_failed = True
            except Exception as exc:
                sys.stderr.write(f"{pkg}: Comparator step failed: {exc}\n")
                step_failed = True

        comp = json.loads((pkg_dir / "comparator.json").read_text(encoding="utf-8"))
        comp_theorems: list[str] = comp.get("theorem_names", [])
        comp_defs: list[str] = comp.get("definition_names", [])
        olean_dir = pkg_dir / ".lake" / "build" / "lib" / "lean"
        t_env_cmp = time.time()
        if (olean_dir / "Challenge.olean").is_file() and (olean_dir / "Solution.olean").is_file():
            env_compare_file = ver_dir / "EnvCompare.lean"
            rel_env_compare = ".verification/EnvCompare.lean"
            env_compare_file.write_text(ENV_COMPARE_LEAN, encoding="utf-8")
            try:
                env_args = [f"--def:{d}" for d in comp_defs] + comp_theorems
                with open(ver_dir / "env_compare.log", "w", encoding="utf-8") as ef:
                    res = subprocess.run(
                        ["lake", "env", "lean", "--run", rel_env_compare] + env_args,
                        cwd=pkg_dir,
                        stdout=ef,
                        stderr=subprocess.STDOUT,
                    )
                if res.returncode != 0:
                    sys.stderr.write((ver_dir / "env_compare.log").read_text(encoding="utf-8", errors="replace"))
                    step_failed = True
            finally:
                if env_compare_file.exists():
                    env_compare_file.unlink()
            fc_rc = run_fc_statement_comparison(
                pkg,
                fc_lib_dir=fc_lib_dir,
                strict=True,
            )
            if fc_rc != 0:
                step_failed = True
        else:
            step_failed = True
        env_cmp_sec = round(time.time() - t_env_cmp, 3)
    finally:
        (ver_dir / "comparator.protected.json").unlink(missing_ok=True)

    rusage = resource.getrusage(resource.RUSAGE_CHILDREN)
    peak_rss_mib = round(rusage.ru_maxrss / 1024.0, 2)
    res_metrics = {
        "verify_sh_seconds": verify_sh_sec,
        "env_compare_and_core_audit_seconds": env_cmp_sec,
        "total_elapsed_seconds": round(time.time() - t_start, 3),
        "user_cpu_seconds": round(rusage.ru_utime, 3),
        "system_cpu_seconds": round(rusage.ru_stime, 3),
        "peak_rss_mib": peak_rss_mib,
    }
    (ver_dir / "resource_usage.json").write_text(
        json.dumps(res_metrics, indent=2) + "\n", encoding="utf-8"
    )

    summary_rc = summarize_package(
        pkg,
        commit,
        repo,
        run_id,
        step_summary,
        require_comparator=run_comparator,
        require_sandbox=(
            run_comparator
            and not force_no_sandbox
            and os.environ.get("GITHUB_ACTIONS") == "true"
        ),
        step_failed=step_failed,
    )
    return 1 if (step_failed or summary_rc != 0) else 0


def finalize_package_receipt(
    pkg: str,
    commit: str,
    repo: str,
    run_id: str,
    step_summary: str | None,
    *,
    require_comparator: bool = False,
) -> int:
    pkg_dir = REPO_ROOT / pkg
    ver_dir = pkg_dir / ".verification"
    ver_dir.mkdir(parents=True, exist_ok=True)
    (ver_dir / "comparator.protected.json").unlink(missing_ok=True)
    if (ver_dir / "VERIFICATION.json").is_file():
        return 0
    summarize_package(
        pkg,
        commit,
        repo,
        run_id,
        step_summary,
        require_comparator=require_comparator,
        step_failed=True,
    )
    return 0


def aggregate_reports(
    artifacts_dir: str,
    expected_packages_json: str,
    output_path: str,
    step_summary: str | None,
) -> int:
    root = pathlib.Path(artifacts_dir)
    expected = json.loads(expected_packages_json) if expected_packages_json.strip() else []
    found: dict[str, dict[str, Any]] = {}
    if root.is_dir():
        for p in sorted(root.rglob("VERIFICATION.json")):
            try:
                data = json.loads(p.read_text(encoding="utf-8"))
                pkg = data.get("package")
                if pkg:
                    found[pkg] = data
            except Exception:
                pass

    missing = [pkg for pkg in expected if pkg not in found]
    failed = [pkg for pkg, rec in sorted(found.items()) if rec.get("status") != "PASS"]
    overall = "PASS" if (not missing and not failed) else "FAIL"

    combined = {
        "schema_version": 2,
        "status": overall,
        "expected_packages": expected,
        "verified_packages": sorted(found.keys()),
        "missing_packages": missing,
        "failed_packages": failed,
        "packages": [found[k] for k in sorted(found.keys())],
    }
    if output_path:
        out_p = pathlib.Path(output_path)
        out_p.parent.mkdir(parents=True, exist_ok=True)
        out_p.write_text(json.dumps(combined, indent=2) + "\n", encoding="utf-8")

    md = [
        f"## Consolidated Verification Gate ({overall})",
        "",
        "| Package | Status | Theorems | Axioms | NanoDa | con-ron | Lean Kernel | Sandbox | Time |",
        "| --- | --- | --- | --- | --- | --- | --- | --- | --- |",
    ]
    for pkg in expected or sorted(found.keys()):
        rec = found.get(pkg)
        if not rec:
            md.append(f"| `{pkg}` | **MISSING** | - | - | - | - | - | - | - |")
            continue
        n_thm = len(rec.get("exported_theorems", []))
        n_ax = f"{rec.get('axiom_audit_count', 0)}/{rec.get('expected_axiom_audit_count', 0)}"
        t_sec = f"{rec.get('resource_usage', {}).get('total_elapsed_seconds', 0):.1f}s"
        md.append(
            f"| `{pkg}` | {rec.get('status')} | `{n_thm}` | `{n_ax}` | "
            f"`{rec.get('nanoda_accepted')}` | `{rec.get('con_ron_accepted')}` | "
            f"`{rec.get('lean_kernel_accepted')}` | `{rec.get('sandbox_enabled')}` | `{t_sec}` |"
        )
    summary_txt = "\n".join(md) + "\n"
    print(summary_txt)
    if step_summary:
        with open(step_summary, "a", encoding="utf-8") as f:
            f.write(summary_txt)
    return 0 if overall == "PASS" else 1


def publish_verification_records(
    records_dir: str,
    *,
    artifacts_dir: str = "",
    packages: list[str] | None = None,
    commit: str = "",
    repo: str = "",
    run_id: str = "",
    force: bool = False,
) -> int:
    out_root = pathlib.Path(records_dir).resolve()
    out_root.mkdir(parents=True, exist_ok=True)

    source_ver_dirs: list[tuple[str, pathlib.Path, dict[str, Any]]] = []
    if artifacts_dir:
        art_root = pathlib.Path(artifacts_dir)
        if art_root.is_dir():
            for vjson in sorted(art_root.rglob("VERIFICATION.json")):
                try:
                    data = json.loads(vjson.read_text(encoding="utf-8"))
                    pkg_name = data.get("package", "")
                    if pkg_name:
                        source_ver_dirs.append((pkg_name, vjson.parent, data))
                except Exception:
                    pass

    if packages:
        for raw_pkg in packages:
            pkg_name = f"erdos-{raw_pkg}" if raw_pkg.isdigit() else raw_pkg
            vdir = REPO_ROOT / pkg_name / ".verification"
            vjson = vdir / "VERIFICATION.json"
            if vjson.is_file():
                try:
                    data = json.loads(vjson.read_text(encoding="utf-8"))
                    source_ver_dirs.append((pkg_name, vdir, data))
                except Exception:
                    pass

    commit_sha = commit.strip()
    if not commit_sha:
        try:
            commit_sha = subprocess.check_output(
                ["git", "-C", str(REPO_ROOT), "rev-parse", "HEAD"],
                text=True,
                stderr=subprocess.DEVNULL,
            ).strip()
        except Exception:
            commit_sha = "local"

    for pkg_name, vdir, data in source_ver_dirs:
        input_sha256 = data.get("input_sha256") or collect_input_sha256(REPO_ROOT / pkg_name)
        state_sha256 = compute_package_state_sha256(pkg_name, input_sha256)
        pkg_commit, commit_date, verification_id = resolve_package_commit_and_id(
            pkg_name, data.get("commit") or commit_sha, state_sha256
        )
        data["state_sha256"] = state_sha256
        data["verification_id"] = verification_id
        data["verification_date"] = commit_date
        data["package_commit"] = pkg_commit
        if commit_sha and not data.get("commit"):
            data["commit"] = commit_sha
        if repo and not data.get("repository"):
            data["repository"] = repo
        if run_id and not data.get("run_id"):
            data["run_id"] = run_id

        pkg_records_dir = out_root / "records" / pkg_name
        pkg_records_dir.mkdir(parents=True, exist_ok=True)
        target_json = pkg_records_dir / f"{verification_id}.json"
        target_md = pkg_records_dir / f"{verification_id}.md"

        if not force and target_json.is_file() and target_md.is_file():
            try:
                existing_data = json.loads(target_json.read_text(encoding="utf-8"))
                if existing_data.get("status") == "PASS":
                    continue
            except Exception:
                pass

        target_json.write_text(
            json.dumps(data, indent=2) + "\n", encoding="utf-8"
        )
        src_md = vdir / "VERIFICATION.md"
        if src_md.is_file():
            md_txt = src_md.read_text(encoding="utf-8", errors="replace")
            md_txt = re.sub(
                r"^- \*\*Verification ID:\*\* `[^`]+`",
                f"- **Verification ID:** `{verification_id}`",
                md_txt,
                count=1,
                flags=re.M,
            )
            target_md.write_text(md_txt, encoding="utf-8")

    # Rebuild cumulative root index.json and README.md across all records/erdos-*/*.json
    prior_history: dict[str, list[str]] = {}
    prior_index_path = out_root / "index.json"
    if prior_index_path.is_file():
        try:
            prior_idx = json.loads(prior_index_path.read_text(encoding="utf-8"))
            for k_pkg, v_entry in (prior_idx.get("packages") or {}).items():
                hist = v_entry.get("verification_history")
                if isinstance(hist, list):
                    prior_history[k_pkg] = [str(x) for x in hist]
        except Exception:
            pass

    all_latest: dict[str, dict[str, Any]] = {}
    all_history_ids: dict[str, list[str]] = {}
    all_commit_maps: dict[str, dict[str, str]] = {}
    records_root = out_root / "records"
    if records_root.is_dir():
        for pkg_dir_rec in sorted(records_root.glob("erdos-*")):
            if not pkg_dir_rec.is_dir():
                continue
            pname = pkg_dir_rec.name
            by_vid: dict[str, dict[str, Any]] = {}
            commit_to_vid: dict[str, str] = {}
            for rjson in sorted(pkg_dir_rec.glob("*.json")):
                try:
                    rdata = json.loads(rjson.read_text(encoding="utf-8"))
                    vid = rdata.get("verification_id") or rjson.stem
                    by_vid[vid] = rdata
                    for c_field in ("package_commit", "commit"):
                        c_val = str(rdata.get(c_field, "")).strip()
                        if len(c_val) == 40:
                            commit_to_vid[c_val] = vid
                except Exception:
                    pass
            if not by_vid:
                continue
            all_commit_maps[pname] = commit_to_vid
            ordered_vids: list[str] = [
                v for v in prior_history.get(pname, []) if v in by_vid
            ]
            for v in sorted(by_vid.keys()):
                if v not in ordered_vids:
                    ordered_vids.append(v)
            # If the package exists in REPO_ROOT, prefer its current state verification_id as the latest
            if (REPO_ROOT / pname).is_dir():
                try:
                    cur_inp = collect_input_sha256(REPO_ROOT / pname)
                    cur_state = compute_package_state_sha256(pname, cur_inp)
                    _, _, cur_vid = resolve_package_commit_and_id(pname, commit_sha, cur_state)
                    if cur_vid in by_vid:
                        ordered_vids = [v for v in ordered_vids if v != cur_vid] + [cur_vid]
                except Exception:
                    pass
            all_history_ids[pname] = ordered_vids
            for vid in ordered_vids:
                rdata = by_vid[vid]
                prev = all_latest.get(pname)
                if prev is None or rdata.get("status") == "PASS" or prev.get("status") != "PASS":
                    all_latest[pname] = rdata

    def _pkg_sort_key(name: str) -> tuple[int, str]:
        m = re.match(r"^erdos-(\d+)$", name)
        return (int(m.group(1)) if m else 10**9, name)

    sorted_pkg_names = sorted(all_latest.keys(), key=_pkg_sort_key)
    index_entries: dict[str, Any] = {}
    readme_rows: list[str] = [
        "# Persistent Proof Verification Records",
        "",
        "This branch stores persistent human-readable (`records/erdos-<N>/<YYYY-MM-DD>-<commit8>.md`) and machine-readable (`records/erdos-<N>/<YYYY-MM-DD>-<commit8>.json`) verification certificates for standalone Lean 4 (`v4.35.0-rc2`, Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`) packages in this repository.",
        "",
        "| Package | Verification ID | Status | Package Commit | Theorems | Axioms | NanoDa | con-ron | Lean Kernel | FC Match | Certificate | Receipt |",
        "| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |",
    ]
    for pname in sorted_pkg_names:
        rec = all_latest[pname]
        vid = rec.get("verification_id") or "unknown"
        c_sha = rec.get("package_commit") or rec.get("commit") or "local"
        c_short = c_sha[:8] if len(c_sha) >= 8 else c_sha
        repo_val = rec.get("repository") or repo
        c_cell = (
            f"[`{c_short}`](https://github.com/{repo_val}/tree/{c_sha}/{pname})"
            if repo_val and len(c_sha) == 40
            else f"`{c_short}`"
        )
        fc_matches = rec.get("fc_statement_audit") or []
        n_thm = len(rec.get("exported_theorems") or [])
        n_ax = f"{rec.get('axiom_audit_count', 0)}/{rec.get('expected_axiom_audit_count', 0)}"
        rel_rec_md = f"records/{pname}/{vid}.md"
        rel_rec_json = f"records/{pname}/{vid}.json"
        index_entries[pname] = {
            "package": pname,
            "verification_id": vid,
            "state_sha256": rec.get("state_sha256", ""),
            "project_name": rec.get("project_name", pname),
            "status": rec.get("status", "UNKNOWN"),
            "package_commit": c_sha,
            "lean_toolchain": rec.get("lean_toolchain", EXPECTED_TOOLCHAIN),
            "mathlib_revision": rec.get("mathlib_revision", EXPECTED_MATHLIB_REV),
            "challenge_sha256": (rec.get("input_sha256") or {}).get("Challenge.lean", ""),
            "solution_sha256": (rec.get("input_sha256") or {}).get("Solution.lean", ""),
            "exported_theorems": rec.get("exported_theorems", []),
            "declaration_lines": rec.get("declaration_lines", {}),
            "kernels": rec.get("kernels", {}),
            "fc_statement_matches": len(fc_matches),
            "record_json": rel_rec_json,
            "record_md": rel_rec_md,
            "commits": all_commit_maps.get(pname, {}),
            "verification_history": all_history_ids.get(pname, [vid]),
        }
        readme_rows.append(
            f"| `{pname}` | `{vid}` | **{rec.get('status', 'UNKNOWN')}** | {c_cell} | `{n_thm}` | `{n_ax}` | "
            f"`{rec.get('nanoda_accepted')}` | `{rec.get('con_ron_accepted')}` | "
            f"`{rec.get('lean_kernel_accepted')}` | `{len(fc_matches)}` | "
            f"[{vid}.md]({rel_rec_md}) | [{vid}.json]({rel_rec_json}) |"
        )

    master_index = {
        "schema_version": 2,
        "lean_toolchain": EXPECTED_TOOLCHAIN,
        "mathlib_revision": EXPECTED_MATHLIB_REV,
        "total_verified_packages": len(sorted_pkg_names),
        "packages": index_entries,
    }
    (out_root / "index.json").write_text(
        json.dumps(master_index, indent=2) + "\n", encoding="utf-8"
    )
    (out_root / "README.md").write_text(
        "\n".join(readme_rows) + "\n", encoding="utf-8"
    )
    print(f"Published verification records for {len(source_ver_dirs)} package(s) (cumulative index: {len(sorted_pkg_names)} package(s)) to {out_root}")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="cmd", required=True)

    p_hyg = sub.add_parser("check", help="Validate package manifests, headers, and metadata")
    p_hyg.add_argument("packages", nargs="*", help="Package names (default: all erdos-*)")

    p_det = sub.add_parser("plan", help="Select target packages and validate manifests")
    p_det.add_argument("--event-name", default="")
    p_det.add_argument("--base-sha", default="")
    p_det.add_argument("--base-ref", default="")
    p_det.add_argument("--head-sha", default="")
    p_det.add_argument("--problems", default="")
    p_det.add_argument("--github-output", default="")

    p_sum = sub.add_parser("summarize", help="Emit VERIFICATION.json and Markdown step summary")
    p_sum.add_argument("--package", required=True)
    p_sum.add_argument("--comparator", action="store_true")
    p_sum.add_argument("--commit", default="")
    p_sum.add_argument("--repo", default="")
    p_sum.add_argument("--run-id", default="")
    p_sum.add_argument("--step-summary", default="")

    p_ver = sub.add_parser("verify", help="Run package verification and emit summary")
    p_ver.add_argument("--package", required=True)
    p_ver.add_argument("--shared-packages", default="")
    p_ver.add_argument("--fc-lib-dir", default="")
    p_ver.add_argument("--comparator", action="store_true")
    p_ver.add_argument("--no-sandbox", action="store_true")
    p_ver.add_argument("--commit", default="")
    p_ver.add_argument("--repo", default="")
    p_ver.add_argument("--run-id", default="")
    p_ver.add_argument("--step-summary", default="")

    p_fcc = sub.add_parser("fc-compare", help="Compare Solution.olean against FormalConjectures or Statement.olean")
    p_fcc.add_argument("--package", default="")
    p_fcc.add_argument("--fc-lib-dir", default="")
    p_fcc.add_argument("--fc-olean", default="")
    p_fcc.add_argument("--sol-olean", default="")
    p_fcc.add_argument("--out-json", default="")
    p_fcc.add_argument("--pairs", nargs="*", default=[])
    p_fcc.add_argument("--strict", action="store_true", help="Fail when upstream FC/Statement coverage is missing or incomplete")

    p_pub = sub.add_parser("publish-records", help="Publish persistent verification records and cumulative index")
    p_pub.add_argument("--records-dir", required=True)
    p_pub.add_argument("--artifacts-dir", default="")
    p_pub.add_argument("--packages", nargs="*", default=[])
    p_pub.add_argument("--commit", default="")
    p_pub.add_argument("--repo", default="")
    p_pub.add_argument("--run-id", default="")
    p_pub.add_argument("--force", action="store_true")

    p_fin = sub.add_parser("finalize", help="Ensure VERIFICATION.json exists after an interrupted job")
    p_fin.add_argument("--package", required=True)
    p_fin.add_argument("--comparator", action="store_true")
    p_fin.add_argument("--commit", default="")
    p_fin.add_argument("--repo", default="")
    p_fin.add_argument("--run-id", default="")
    p_fin.add_argument("--step-summary", default="")

    p_agg = sub.add_parser("aggregate", help="Aggregate per-package VERIFICATION.json artifacts")
    p_agg.add_argument("--artifacts-dir", required=True)
    p_agg.add_argument("--expected-packages", default="[]")
    p_agg.add_argument("--output", required=True)
    p_agg.add_argument("--step-summary", default="")

    args = parser.parse_args()

    if args.cmd == "check":
        pkgs = args.packages
        if not pkgs or (len(pkgs) == 1 and pkgs[0].lower() == "all"):
            pkgs = all_packages()
        all_errs: list[str] = []
        for pkg in pkgs:
            all_errs.extend(check_package_manifest(pkg))
        if all_errs:
            for err in all_errs:
                print(f"FAIL: {err}", file=sys.stderr)
            return 1
        print(f"PASS: preflight and manifest checks passed for {len(pkgs)} package(s)")
        return 0

    if args.cmd == "plan":
        pkgs = detect_changed_packages(
            args.event_name,
            args.base_sha,
            args.head_sha,
            args.problems,
            args.base_ref,
        )
        check_targets = all_packages()
        all_errs = []
        for pkg in check_targets:
            all_errs.extend(check_package_manifest(pkg))
        if all_errs:
            for err in all_errs:
                print(f"FAIL: {err}", file=sys.stderr)
            return 1
        print(f"Detected packages ({len(pkgs)}): {pkgs}")
        if args.github_output:
            with open(args.github_output, "a", encoding="utf-8") as f:
                f.write(f"packages={json.dumps(pkgs)}\n")
                f.write(f"has_packages={'true' if pkgs else 'false'}\n")
        return 0

    if args.cmd == "summarize":
        return summarize_package(
            args.package,
            args.commit,
            args.repo,
            args.run_id,
            args.step_summary or None,
            require_comparator=args.comparator,
        )

    if args.cmd == "verify":
        return run_package_verification(
            args.package,
            args.shared_packages or None,
            args.comparator or args.no_sandbox,
            args.commit,
            args.repo,
            args.run_id,
            args.step_summary or None,
            force_no_sandbox=args.no_sandbox,
            fc_lib_dir=args.fc_lib_dir or None,
        )

    if args.cmd == "fc-compare":
        return run_fc_statement_comparison(
            args.package,
            fc_lib_dir=args.fc_lib_dir or None,
            fc_olean=args.fc_olean or None,
            sol_olean=args.sol_olean or None,
            pairs=args.pairs or None,
            out_json=args.out_json or None,
            strict=args.strict,
        )

    if args.cmd == "publish-records":
        return publish_verification_records(
            args.records_dir,
            artifacts_dir=args.artifacts_dir,
            packages=args.packages,
            commit=args.commit,
            repo=args.repo,
            run_id=args.run_id,
            force=args.force,
        )

    if args.cmd == "finalize":
        return finalize_package_receipt(
            args.package,
            args.commit,
            args.repo,
            args.run_id,
            args.step_summary or None,
            require_comparator=args.comparator,
        )

    if args.cmd == "aggregate":
        return aggregate_reports(
            args.artifacts_dir,
            args.expected_packages,
            args.output,
            args.step_summary or None,
        )

    return 1


if __name__ == "__main__":
    sys.exit(main())
