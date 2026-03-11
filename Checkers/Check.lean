import Lean.Meta

def main (args : List String) : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  let (temp_data, _) ← Lean.readModuleData (← Lean.findOLean args[0]!.toName)
  let (subm_data, _) ← Lean.readModuleData (← Lean.findOLean args[1]!.toName)
  let subm_env ← Lean.importModules subm_data.imports {} 0
  Prod.fst <$> (Lean.Meta.MetaM.toIO · {fileName := "", fileMap := default} {env := subm_env}) do
    for temp_const in temp_data.constants do
      match subm_data.constants.find? (·.name = temp_const.name) with
      | none => IO.Process.exit 1
      | some subm_const =>
        if ¬ (← Lean.Meta.isDefEq subm_const.type temp_const.type) then
          IO.Process.exit 1
        match temp_const, subm_const with
        | .defnInfo temp_def, .defnInfo subm_def =>
          if temp_const.name = `answer then continue
          if ¬ (← Lean.Meta.isDefEq subm_def.value temp_def.value) then
            IO.Process.exit 1
        | .thmInfo _, .thmInfo _ => continue
        | _, _  => IO.Process.exit 1
