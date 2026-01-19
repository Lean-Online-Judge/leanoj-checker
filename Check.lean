import Lean.CoreM
import Lean.Replay
import Lean.Environment
import Lean.Util.CollectAxioms

def main (args : List String) : IO UInt32 := do
  let pref ← IO.currentDir

  let LEAN_PATH : String := s!"{pref}/.lake/packages/batteries/.lake/build/lib/lean:{pref}/.lake/packages/Qq/.lake/build/lib/lean:{pref}/.lake/packages/aesop/.lake/build/lib/lean:{pref}/.lake/packages/proofwidgets/.lake/build/lib/lean:{pref}/.lake/packages/importGraph/.lake/build/lib/lean:{pref}/.lake/packages/mathlib/.lake/build/lib/lean:{pref}/.lake/packages/plausible/.lake/build/lib/lean:{pref}/.lake/packages/LeanSearchClient/.lake/build/lib/lean:"

  let child ← IO.Process.spawn {
    cmd := "lean"
    args := #[args[1]!, "-o", "template.olean"]
    cwd := args[0]!
    env := #[⟨"LEAN_PATH", LEAN_PATH⟩]
--    stdout := .null
--    stderr := .null
  }

  let templExitCode ← child.wait
  if templExitCode ≠ 0 then
     IO.println "bad template"
     return 43

  let child ← IO.Process.spawn {
    cmd := "lean"
    args := #[args[2]!, "-o", "submission.olean"]
    cwd := args[0]!
    env := #[⟨"LEAN_PATH", LEAN_PATH⟩]
--    stdout := .null
--    stderr := .null
  }

  let submExitCode ← child.wait
  if submExitCode ≠ 0 then
     IO.println "compilation error"
     return 44

  Lean.initSearchPath (← Lean.findSysroot) [args[0]!]

  let templEnv ← Lean.importModules #[{module := `template}] {}
  match templEnv.find? `solution with
  | none =>
      IO.println "bad template"
      return 45
  | some templ =>
    let (mod, _) ← Lean.readModuleData (System.FilePath.join args[0]! "submission.olean")
    let (_, state) ← Lean.importModulesCore mod.imports |>.run
    let submEnv ← Lean.finalizeImport state #[{module := `submission}] {} 0 true true
    let mut newConstants := {}
    for name in mod.constNames, ci in mod.constants do
      newConstants := newConstants.insert name ci

    let task ← IO.asTask (submEnv.replay newConstants)
    match task.get with
    | .error _ =>
        IO.println "environment error"
        return 45
    | .ok submEnv =>
        match submEnv.find? `solution with
        | none =>
          IO.println "solution not found"
          return 46
        | some sol =>
          if templ.type != sol.type then
            IO.println "solution type mismatch"
            return 47
          else
           let (_, state) := ((Lean.CollectAxioms.collect templ.name).run submEnv).run {}
           for ax in state.axioms do
             if ax ∉ [`propext, `Quot.sound, `Classical.choice] then
                IO.println "forbidden axiom"
                return 48
           IO.println ":tada"
           return 42
