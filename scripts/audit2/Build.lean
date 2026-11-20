import Lake.CLI.Main

/-- Run the normal Lake CLI with an on-disk target list. This avoids the OS
argument limit without repeatedly rebuilding the same dependency graph. -/
def main (args : List String) : IO UInt32 := do
  let targets :: opts := args | throw <| IO.userError "Build.lean TARGETS [LAKE OPTIONS]"
  let modules ← IO.FS.lines targets
  if modules.isEmpty || modules.any (·.isEmpty) then
    throw <| IO.userError "expected a nonempty list of modules, one per line"
  Lake.cli ("build" :: opts ++ modules.toList.map ("+" ++ ·))
