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

  IO.println "Compiling template..."

  let child ← IO.Process.spawn {
    cmd := "lean"
    args := #["template.lean", "-o", "template.olean"]
    cwd := work_dir
    env := #[⟨"LEAN_PATH", LEAN_PATH⟩]
    -- stdout := .null
    -- stderr := .null
  }

  let exit_code ← child.wait
  if exit_code ≠ 0 then
    IO.println "Template error"
    IO.Process.exit 43

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

  Lean.withImportModules #[{module := `template}] {} (trustLevel := 1024) fun template_env =>
    Lean.withImportModules #[{module := `submission}] {} (trustLevel := 1024) fun submission_env => do
      let template_ctx := { fileName := "", fileMap := default }
      let template_state := { env := template_env }
      let template_infos ← Prod.fst <$> (Lean.Core.CoreM.toIO · template_ctx template_state) do
        let mut infos : Lean.ConstMap := {}
        let decls ← Batteries.Tactic.Lint.getDeclsInPackage `template
        for decl in decls do
          if not decl.isInternal then
            infos := infos.insert decl (← Lean.getConstInfo decl)
        pure infos

      let submission_ctx := { fileName := "", fileMap := default }
      let submission_state := { env := submission_env }
      let submission_infos ← Prod.fst <$> (Lean.Core.CoreM.toIO · submission_ctx submission_state) do
        let mut infos : Lean.ConstMap := {}
        let decls ← Batteries.Tactic.Lint.getDeclsInPackage `submission
        for decl in decls do
          if ¬ decl.isInternal then
            for ax in (← Lean.collectAxioms decl) do
              if ax ∉ [``propext, ``Classical.choice, ``Quot.sound] then
                IO.println "Forbidden axiom"
                IO.Process.exit 46
            infos := infos.insert decl (← Lean.getConstInfo decl)
        pure infos

      Prod.fst <$> (Lean.Meta.MetaM.toIO · submission_ctx submission_state) do
        for (decl, template_info) in template_infos do
          match submission_infos.find? decl with
          | none =>
            IO.println s!"Template mismatch"
            IO.Process.exit 45
          | some submission_info =>
            match template_info, submission_info with
            | .defnInfo template_def, .defnInfo submission_def =>
              if ¬ (← Lean.Meta.isDefEq template_def.type submission_def.type) then
                IO.println "Template mismatch"
                IO.Process.exit 45
              if ¬ (← Lean.Meta.isDefEq template_def.value submission_def.value) ∧ decl ≠ `answer then
                IO.println "Template mismatch"
                IO.Process.exit 45
            | .thmInfo template_thm, .thmInfo submission_thm =>
              if ¬ (← Lean.Meta.isDefEq template_thm.type submission_thm.type) then
                IO.println "Template mismatch"
                IO.Process.exit 45
            | _, _  =>
              IO.println "Template mismatch"
              IO.Process.exit 45

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
