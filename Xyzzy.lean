import Lean.CoreM
import Lean.Replay
import Lean.Meta
import Lean.Environment
import Lean.Util.CollectAxioms
import Batteries.Tactic.Lint

-- heavily inpsired by Compfiles

unsafe def main (args : List String) : IO UInt32 := do
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
     IO.Process.exit 44

  Lean.initSearchPath (← Lean.findSysroot) [work_dir]

  IO.println "Checking declarations..."

  Lean.withImportModules #[{module := `submission}] {} (trustLevel := 1024) fun submission_env => do
    let submission_ctx := { fileName := "", fileMap := default }
    let submission_state := { env := submission_env }
    Prod.fst <$> (Lean.Core.CoreM.toIO · submission_ctx submission_state) do
      let decls ← Batteries.Tactic.Lint.getDeclsInPackage `submission
      for decl in decls do
        if ¬ decl.isInternal then
          for ax in (← Lean.collectAxioms decl) do
            if ax ∉ [``propext, ``Classical.choice, ``Quot.sound] then
              IO.println "Forbidden axiom"
              IO.Process.exit 46

  IO.println "Replaying environment..."

  let mod := Prod.fst <| ← Lean.readModuleData (← Lean.findOLean `submission)
  let state := Prod.snd (← Lean.importModulesCore mod.imports |>.run)
  let mut env ← Lean.finalizeImport state #[{module := `submission}] {} 0 true true
  let mut infos : Std.HashMap Lean.Name Lean.ConstantInfo := {}
  for decl in mod.constNames, info in mod.constants do
    infos := infos.insert decl info

  try
    let _ ← env.replay infos
  catch _ =>
    IO.println "Environment error"
    IO.Process.exit 47

  return 42
