#!/usr/bin/env python3
"""CI package selection, manifest validation, environment comparison, and summary generator."""

from __future__ import annotations

import argparse
import json
import os
import pathlib
import re
import subprocess
import sys
import tomllib
from typing import Any

REPO_ROOT = pathlib.Path(__file__).resolve().parents[2]
EXPECTED_TOOLCHAIN = "leanprover/lean4:v4.35.0-rc2"
EXPECTED_MATHLIB_REV = "065356127b1dc0016f66b7283ce0ce2c4055aa55"
PERMITTED_AXIOMS = ["propext", "Classical.choice", "Quot.sound"]
VALID_SOURCE_RELS = {"formalizes", "adapts", "independently-proves"}

SKIP_DIRS = {".git", ".lake", ".verification", "verification", "verification-local"}
FORBIDDEN_SUFFIXES = (".swp", ".swo", ".swn", "~", ".olean", ".ilean", ".ir", ".trace")
DOC_ONLY_FILENAMES = {
    "README.md",
    "BUILD.md",
    "THIRD_PARTY.md",
    "LICENSE",
    ".gitignore",
    "formalization.yaml",
}

ENV_COMPARE_LEAN = """import Lean
open Lean

def moduleOfConst (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some idx => env.header.moduleNames.getD idx.toNat Name.anonymous
  | none => Name.anonymous

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

unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot) [System.FilePath.mk ".lake/build/lib/lean"]
  let rawC ← importModules #[{ module := `Challenge, importAll := true }] {} 0
  let rawS ← importModules #[{ module := `Solution, importAll := true }] {} 0
  let envC := rawC.setExporting false
  let envS := rawS.setExporting false
  if envS.allImportedModuleNames.contains `Challenge then
    throw <| IO.userError "Solution must not import Challenge"
  let targetThms : NameSet := args.foldl (fun acc raw => acc.insert raw.toName) {}
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
  for raw in args do
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
  return 0
"""


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
            manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
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
            comp = json.loads(comp_path.read_text(encoding="utf-8"))
            fy = json.loads(fy_path.read_text(encoding="utf-8"))
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
            proj = fy.get("project", {})
            if proj.get("license") != "Apache-2.0":
                errors.append(
                    f"{pkg}: formalization.yaml project.license is {proj.get('license')!r}, expected 'Apache-2.0'"
                )
            methods = fy.get("automation", {}).get("methods", [])
            if not methods or methods[0].get("method") != "agent":
                errors.append(f"{pkg}: formalization.yaml automation.methods[0].method must be 'agent'")
            sources = fy.get("sources", [])
            if not any(s.get("relationship") in VALID_SOURCE_RELS for s in sources):
                errors.append(
                    f"{pkg}: formalization.yaml needs a source with relationship in {sorted(VALID_SOURCE_RELS)}"
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

    for root, dirs, files in os.walk(pkg_dir):
        dirs[:] = [d for d in dirs if d not in SKIP_DIRS and not d.startswith(".lake-") and not d.startswith(".verification-")]
        root_path = pathlib.Path(root)
        for fname in files:
            fpath = root_path / fname
            rel = fpath.relative_to(REPO_ROOT)
            if fname == ".DS_Store" or fname.endswith(FORBIDDEN_SUFFIXES):
                errors.append(f"{rel}: forbidden temporary or build file")
                continue
            txt = fpath.read_text(encoding="utf-8", errors="replace")
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


def summarize_package(
    pkg: str,
    commit: str,
    repo: str,
    run_id: str,
    step_summary: str | None,
    *,
    require_comparator: bool = False,
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
    lean_kernel_ok = "Lean default kernel accepts the solution" in comp_log

    bad_axioms = [
        (decl, axs)
        for decl, axs in axiom_pairs
        if any(a not in PERMITTED_AXIOMS for a in axs)
    ]
    missing_from_axioms = [t for t in comp_theorems if t not in axiom_map]
    missing_from_env = [t for t in comp_theorems if t not in env_matched]
    comparator_ok = (
        (bool(comp_log) and nanoda_ok and lean_kernel_ok)
        if require_comparator
        else ((not comp_log) or (nanoda_ok and lean_kernel_ok))
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
            and comparator_ok
        )
        else "FAIL"
    )

    receipt: dict[str, Any] = {
        "package": pkg,
        "project_name": fy.get("project", {}).get("name", pkg),
        "commit": commit,
        "repository": repo,
        "run_id": run_id,
        "lean_toolchain": toolchain_txt,
        "mathlib_revision": EXPECTED_MATHLIB_REV,
        "exported_theorems": comp_theorems,
        "env_comparison_matched": sorted(env_matched),
        "missing_from_axioms_log": missing_from_axioms,
        "missing_from_env_compare": missing_from_env,
        "axiom_audit_count": len(axiom_pairs),
        "expected_axiom_audit_count": expected_axiom_reports,
        "axiom_reports": [
            {"declaration": decl, "axioms": axs} for decl, axs in axiom_pairs
        ],
        "comparator_required": require_comparator,
        "comparator_ran": bool(comp_log),
        "nanoda_accepted": nanoda_ok,
        "lean_kernel_accepted": lean_kernel_ok,
        "status": status,
    }
    ver_dir.mkdir(parents=True, exist_ok=True)
    (ver_dir / "VERIFICATION.json").write_text(
        json.dumps(receipt, indent=2) + "\n", encoding="utf-8"
    )

    md_lines = [
        f"## `{pkg}` Verification Summary ({status})",
        "",
        f"- **Project:** {fy.get('project', {}).get('name', pkg)}",
        f"- **Commit:** `{commit}`" + (f" ([tree](https://github.com/{repo}/tree/{commit}/{pkg}))" if repo and commit else ""),
        f"- **Compiler:** `{toolchain_txt}`",
        f"- **Mathlib:** `{EXPECTED_MATHLIB_REV}`",
        f"- **Challenge ↔ Solution environment match:** `{len(env_matched)}/{len(comp_theorems)}` theorems",
        f"- **Endpoint `#print axioms` checks:** `{len(axiom_pairs)}/{expected_axiom_reports}` (permitted: `propext`, `Classical.choice`, `Quot.sound`)",
    ]
    if comp_log or require_comparator:
        md_lines.append(
            f"- **Comparator:** NanoDa=`{nanoda_ok}`, Lean default kernel=`{lean_kernel_ok}`"
        )
    if bad_axioms:
        md_lines.append(f"- **DISALLOWED axioms:** `{bad_axioms}`")
    if missing_from_axioms:
        md_lines.append(f"- **MISSING from `axioms.log`:** `{missing_from_axioms}`")
    if missing_from_env:
        md_lines.append(f"- **MISSING from `Challenge`/`Solution` match:** `{missing_from_env}`")
    md_lines.extend([
        "",
        "### Exported Theorems & Axiom Footprint",
        "",
        "| Declaration | Challenge = Solution | Axioms |",
        "| --- | --- | --- |",
    ])
    for thm in comp_theorems:
        axs = axiom_map.get(thm)
        axs_str = (
            ", ".join(f"`{a}`" for a in axs)
            if axs
            else ("`none`" if axs == [] else "**MISSING**")
        )
        matched_str = "PASS" if thm in env_matched else "**FAIL**"
        md_lines.append(f"| `{thm}` | {matched_str} | {axs_str} |")

    summary_md = "\n".join(md_lines) + "\n"
    print(summary_md)
    if step_summary:
        with open(step_summary, "a", encoding="utf-8") as f:
            f.write(summary_md)

    return 0 if status == "PASS" else 1


def run_package_verification(
    pkg: str,
    shared_packages: str | None,
    run_comparator: bool,
    commit: str,
    repo: str,
    run_id: str,
    step_summary: str | None,
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
        "VERIFICATION.json",
    ):
        stale_path = ver_dir / stale
        if stale_path.exists():
            stale_path.unlink()

    step_failed = False
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
    if not step_failed and verify_sh.is_file():
        cmd = ["./verify.sh"]
        if run_comparator:
            cmd.append("--no-sandbox")
        res_v = subprocess.run(cmd, cwd=pkg_dir)
        if res_v.returncode != 0:
            step_failed = True
            for log_name in ("build.log", "axioms.log", "comparator.log"):
                log_path = ver_dir / log_name
                if log_path.is_file():
                    sys.stderr.write(f"--- {log_name} ---\n")
                    sys.stderr.write(log_path.read_text(encoding="utf-8", errors="replace"))
    elif not step_failed:
        try:
            tc_out = subprocess.check_output(["lake", "env", "lean", "--version"], cwd=pkg_dir, text=True)
            (ver_dir / "toolchain.log").write_text(tc_out, encoding="utf-8")
            if "version 4.35.0-rc2," not in tc_out:
                sys.stderr.write(f"{pkg}: unexpected compiler version: {tc_out.strip()}\n")
                step_failed = True
            ml_rev = subprocess.check_output(
                ["git", "-C", str(lake_pkgs / "mathlib"), "rev-parse", "HEAD"],
                text=True,
            ).strip()
            if ml_rev != EXPECTED_MATHLIB_REV:
                sys.stderr.write(f"{pkg}: unexpected Mathlib revision: {ml_rev}\n")
                step_failed = True
        except subprocess.CalledProcessError as exc:
            sys.stderr.write(f"{pkg}: toolchain/mathlib check failed: {exc}\n")
            step_failed = True

        if not step_failed:
            build_targets = ["Challenge", "Solution", "AxiomAudit"]
            if (pkg_dir / "Statement.lean").is_file():
                build_targets.insert(0, "Statement")
            with open(ver_dir / "build.log", "w", encoding="utf-8") as bf:
                res_b = subprocess.run(
                    ["lake", "build", *build_targets],
                    cwd=pkg_dir,
                    stdout=bf,
                    stderr=subprocess.STDOUT,
                )
            if res_b.returncode != 0:
                sys.stderr.write((ver_dir / "build.log").read_text(encoding="utf-8", errors="replace"))
                step_failed = True

        if not step_failed:
            with open(ver_dir / "axioms.log", "w", encoding="utf-8") as af:
                res_a = subprocess.run(
                    [
                        "lake",
                        "env",
                        "lean",
                        "-j1",
                        "-M8192",
                        "-E",
                        "hasSorry",
                        "-Dformat.width=1000000",
                        "--setup=.lake/build/ir/AxiomAudit.setup.json",
                        "AxiomAudit.lean",
                    ],
                    cwd=pkg_dir,
                    stdout=af,
                    stderr=subprocess.STDOUT,
                )
            if res_a.returncode != 0:
                sys.stderr.write((ver_dir / "axioms.log").read_text(encoding="utf-8", errors="replace"))
                step_failed = True

        if not step_failed and run_comparator:
            with open(ver_dir / "comparator.log", "w", encoding="utf-8") as cf:
                res_c = subprocess.run(
                    [
                        "lake",
                        "env",
                        "lake",
                        "comparator",
                        "--config",
                        "comparator.json",
                        "--inadvisably-no-sandbox",
                    ],
                    cwd=pkg_dir,
                    stdout=cf,
                    stderr=subprocess.STDOUT,
                )
            if res_c.returncode != 0:
                sys.stderr.write((ver_dir / "comparator.log").read_text(encoding="utf-8", errors="replace"))
                step_failed = True

    comp = json.loads((pkg_dir / "comparator.json").read_text(encoding="utf-8"))
    comp_theorems: list[str] = comp.get("theorem_names", [])
    olean_dir = pkg_dir / ".lake" / "build" / "lib" / "lean"
    if (olean_dir / "Challenge.olean").is_file() and (olean_dir / "Solution.olean").is_file():
        env_compare_file = ver_dir / "EnvCompare.lean"
        rel_env_compare = ".verification/EnvCompare.lean"
        env_compare_file.write_text(ENV_COMPARE_LEAN, encoding="utf-8")
        try:
            with open(ver_dir / "env_compare.log", "w", encoding="utf-8") as ef:
                res = subprocess.run(
                    ["lake", "env", "lean", "--run", rel_env_compare] + comp_theorems,
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
    else:
        step_failed = True

    summary_rc = summarize_package(
        pkg,
        commit,
        repo,
        run_id,
        step_summary,
        require_comparator=run_comparator,
        step_failed=step_failed,
    )
    return 1 if (step_failed or summary_rc != 0) else 0


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
    p_ver.add_argument("--comparator", action="store_true")
    p_ver.add_argument("--commit", default="")
    p_ver.add_argument("--repo", default="")
    p_ver.add_argument("--run-id", default="")
    p_ver.add_argument("--step-summary", default="")

    args = parser.parse_args()

    if args.cmd == "check":
        pkgs = args.packages or all_packages()
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
            args.comparator,
            args.commit,
            args.repo,
            args.run_id,
            args.step_summary or None,
        )

    return 1


if __name__ == "__main__":
    sys.exit(main())
