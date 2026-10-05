module

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
