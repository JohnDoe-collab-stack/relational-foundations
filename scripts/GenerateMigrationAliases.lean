import Lean
import RelationalFoundations
open Lean Elab Command

elab "#generate_migration_aliases" : command => do
  let env ← getEnv
  for (source, target, file, header) in [
      ("RelationalFoundations.ExactTransport", "ExactTypeTransport", "ExactTypeTransport.lean",
        "import RelationalFoundations.ExactTransport\nset_option linter.defProp false\nuniverse u v\nabbrev ExactTypeTransport (A : Type u) (B : Type v) := RelationalFoundations.ExactTransport A B\n"),
      ("RelationalFoundations.Residual", "SegmentedResidualRole", "SegmentedResidualRole.lean",
        "import RelationalFoundations.Residual\nset_option linter.defProp false\n"),
      ("RelationalFoundations.Diagnostics", "AbstractSegmentedTurning", "AbstractSegmentedTurning.lean",
        "import RelationalFoundations.Diagnostics\nset_option linter.defProp false\n"),
      ("RelationalFoundations.History", "StrongPerimetralTurning.History", "Constitution/HistoryAPI.lean",
        "import RelationalFoundations.History\nset_option linter.defProp false\nnamespace StrongPerimetralTurning\nexport RelationalFoundations (History)\nend StrongPerimetralTurning\n")] do
    let mut text := header ++ "set_option linter.checkUnivs false\n"
    let names := env.constants.toList.map Prod.fst |>.filter fun name =>
      name.toString.startsWith (source ++ ".") &&
      (env.getModuleIdxFor? name |>.map (fun idx => env.header.moduleNames[idx.toNat]!.toString ==
        (if source == "RelationalFoundations.ExactTransport" then "RelationalFoundations.ExactTransport" else
        if source == "RelationalFoundations.History" then "RelationalFoundations.History" else source)) |>.getD false) &&
      ((name.toString.splitOn ".").all fun part => !part.isEmpty && part.toList.all fun ch => ch.isAlphanum || ch == '_')
    for name in names do
      let parent := name.getPrefix.toString
      let suffix := parent.drop source.length |>.toString
      let leaf := name.toString.splitOn "." |>.getLast!
      unless (name.toString.splitOn ".").any (fun part =>
          part.startsWith "_" || part.startsWith "match_" || part.startsWith "proof_" ||
          ["rec", "recOn", "casesOn", "brecOn", "below", "ibelow", "noConfusion", "noConfusionType"].contains part) do
        text := text ++ "namespace " ++ target ++ suffix ++ "\nexport " ++ parent ++ " («" ++ leaf ++ "»)\nend " ++ target ++ suffix ++ "\n"
    liftIO <| IO.FS.writeFile ("Migration/" ++ file) text
#generate_migration_aliases
