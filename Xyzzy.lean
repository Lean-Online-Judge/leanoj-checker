import Lean.CoreM
import Lean.Replay
import Lean.Meta
import Lean.Environment
import Lean.Util.CollectAxioms
import Batteries.Tactic.Lint

-- heavily inspired by Compfiles

def main (args : List String) : IO UInt32 := do
  let pref ← IO.currentDir
  let LEAN_PATH : String := String.join [
    s!"{pref}/.lake/packages/batteries/.lake/build/lib/lean:",
    s!"{pref}/.lake/packages/Qq/.lake/build/lib/lean:",
    s!"{pref}/.lake/packages/aesop/.lake/build/lib/lean:",
    s!"{pref}/.lake/packages/proofwidgets/.lake/build/lib/lean:",
    s!"{pref}/.lake/packages/importGraph/.lake/build/lib/lean:",
    s!"{pref}/.lake/packages/mathlib/.lake/build/lib/lean:",
    s!"{pref}/.lake/packages/plausible/.lake/build/lib/lean:",
    s!"{pref}/.lake/packages/LeanSearchClient/.lake/build/lib/lean:"
  ]
  let work_dir := args[0]!

  IO.println "Compiling submission..."

  let child ← IO.Process.spawn {
    cmd := "lean"
    args := #["submission.lean", "-o", "submission.olean"]
    cwd := work_dir
    env := #[⟨"LEAN_PATH", LEAN_PATH⟩]
    -- stdout := .null
    -- stderr := .null
  }

  let exit_code ← child.wait
  if exit_code ≠ 0 then
     IO.println "Compilation error"
     IO.Process.exit 45

  Lean.initSearchPath (← Lean.findSysroot) [work_dir]

  IO.println "Extracting constants..."

  let mod := Prod.fst (← Lean.readModuleData (← Lean.findOLean `submission))
  let state := Prod.snd (← (Lean.importModulesCore mod.imports).run)
  let mut base_env ← Lean.finalizeImport state #[{module := `submission}] {} 0 true true

  let subm_consts := mod.constants
  IO.println "Replaying environment..."

  let mut tmp := {}
  for const in subm_consts do
    tmp := tmp.insert const.name const
  let env ← try base_env.replay tmp
  catch _ =>
    IO.println "Environment error"
    IO.Process.exit 46

  Prod.fst <$> (Lean.Meta.MetaM.toIO · {fileName := "", fileMap := default} {env := env}) do
    IO.println "Checking axioms..."
    for const in subm_consts do
      for ax in ← Lean.collectAxioms const.name do
        if ax ∉ [``propext, ``Classical.choice, ``Quot.sound] then
          IO.println "Forbidden axiom"
          IO.Process.exit 47

  IO.println ":tada"
  return 42
