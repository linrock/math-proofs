module

/-
Copyright 2026 Linmiao Xu.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

public import Lean

public meta section

open Lean Parser Elab Command

namespace Architect

/-! We define the `blueprint_comment /-- ... -/` command that adds a piece of text to the blueprint. -/

-- The moduleBlueprintDocExt is exactly the same as the moduleDocExt, except it stores module docstrings
-- that are preceded by "blueprint ".

initialize moduleBlueprintDocExt :
    SimplePersistentEnvExtension ModuleDoc (PersistentArray ModuleDoc) ← registerSimplePersistentEnvExtension {
  addImportedFn := fun _ => {}
  addEntryFn    := fun s e => s.push e
  exportEntriesFnEx? := some fun _ _ es =>
    let ents := es.toArray
    { exported := #[], server := ents, «private» := ents }
}

def addMainModuleBlueprintDoc (env : Environment) (doc : ModuleDoc) : Environment :=
  moduleBlueprintDocExt.addEntry env doc

def getMainModuleBlueprintDoc (env : Environment) : PersistentArray ModuleDoc :=
  moduleBlueprintDocExt.getState env

def getModuleBlueprintDoc? (env : Environment) (moduleName : Name) : Option (Array ModuleDoc) :=
  env.getModuleIdx? moduleName |>.map fun modIdx =>
    moduleBlueprintDocExt.getModuleEntries (level := .server) env modIdx

/--
`blueprint_comment /-- ... -/` adds a piece of text to the blueprint of the current module,
which is available as `\inputleanmodule{Module}` in LaTeX.
-/
elab (name := blueprintComment) "blueprint_comment " stx:plainDocComment : command => do
  let some range ← Elab.getDeclarationRange? stx
    | return  -- must be from partial syntax, ignore

  let doc ← getDocStringText ⟨stx⟩
  modifyEnv fun env => addMainModuleBlueprintDoc env ⟨doc, range⟩

end Architect
