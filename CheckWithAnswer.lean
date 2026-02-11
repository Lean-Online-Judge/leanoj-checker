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
    IO.println "Judge error"
    IO.Process.exit 44

  IO.println "Compiling answer..."

  let child ← IO.Process.spawn {
    cmd := "lean"
    args := #["answer.lean", "-o", "answer.olean"]
    cwd := work_dir
    env := #[⟨"LEAN_PATH", LEAN_PATH⟩]
    -- stdout := .null
    -- stderr := .null
  }

  let exit_code ← child.wait
  if exit_code ≠ 0 then
    IO.println "Judge error"
    IO.Process.exit 44

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

  let temp_consts := (Prod.fst (← Lean.readModuleData (← Lean.findOLean `template))).constants
  let ans_consts := (Prod.fst (← Lean.readModuleData (← Lean.findOLean `answer))).constants
  let ans_def ← do
    match ans_consts.find? (·.name = `answer) with
    | none =>
      IO.println "Judge error"
      IO.Process.exit 44
    | some const =>
      match const with
      | .defnInfo val =>
        pure val
      | _ =>
        IO.println "Judge error"
        IO.Process.exit 44

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

    IO.println "Checking declarations..."

    for temp_const in temp_consts do
      match subm_consts.find? (·.name = temp_const.name) with
      | none =>
        IO.println "Template mismatch"
        IO.Process.exit 48
      | some subm_const =>
        if ¬ (← Lean.Meta.isDefEq subm_const.type temp_const.type) then
          IO.println "Template mismatch"
          IO.Process.exit 48
        match temp_const, subm_const with
        | .defnInfo temp_def, .defnInfo subm_def =>
          if subm_const.name = `answer then
            if ¬ (← Lean.Meta.isDefEq subm_def.value ans_def.value) then
              IO.println "Bad answer"
              IO.Process.exit 49
          else if ¬ (← Lean.Meta.isDefEq subm_def.value temp_def.value) then
            IO.println "Template mismatch"
            IO.Process.exit 48
        | .thmInfo temp_thm, .thmInfo subm_thm =>
          if ¬ (← Lean.Meta.isDefEq temp_thm.type subm_thm.type) then
            IO.println "Template mismatch"
            IO.Process.exit 48
        | _, _  =>
          IO.println "Template mismatch"
          IO.Process.exit 48

  IO.println ":tada"
  return 42
