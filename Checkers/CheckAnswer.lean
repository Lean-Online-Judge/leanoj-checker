import Lean.Meta

def main (args : List String) : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  let (ans_data, _) ← Lean.readModuleData (← Lean.findOLean args[0]!.toName)
  let (subm_data, _) ← Lean.readModuleData (← Lean.findOLean args[1]!.toName)
  let subm_env ← Lean.importModules subm_data.imports {} 0
  Prod.fst <$> (Lean.Meta.MetaM.toIO · {fileName := "", fileMap := default} {env := subm_env}) do
    for ans_const in ans_data.constants do
      match subm_data.constants.find? (·.name = ans_const.name) with
      | none =>
        IO.Process.exit 1
      | some subm_const =>
        if ¬ (← Lean.Meta.isDefEq subm_const.type ans_const.type) then
          IO.Process.exit 1
        match ans_const, subm_const with
        | .defnInfo ans_def, .defnInfo subm_def =>
          if ¬ (← Lean.Meta.isDefEq subm_def.value ans_def.value) then
            IO.Process.exit 1
        | _, _  => 
          IO.Process.exit 1
