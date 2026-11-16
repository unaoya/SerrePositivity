import VersoManual
import VersoBlueprint.PreviewManifest
import KerodonBlueprint.Blueprint

open Verso Doc
open Verso.Genre Manual

def main (args : List String) : IO UInt32 :=
  Informal.PreviewManifest.blueprintMainWithPreviewData
    (%doc KerodonBlueprint.Blueprint)
    args
    (extensionImpls := by exact extension_impls%)
