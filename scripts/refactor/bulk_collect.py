#!/usr/bin/env python3
"""Collect B2 references with sequential resolution of plain open operands.
Uses the shared collector unchanged on disk and retains its Lake setup handling.
Run under the normal build lease, just like klw1_namespace.py collect.
"""
from pathlib import Path
from tempfile import TemporaryDirectory
import argparse,os,sys
HERE=Path(__file__).resolve().parent
sys.path.insert(0,os.environ.get('BULK_REFACTOR_TOOLS',str(HERE)))
import klw1_namespace as K
OLD='    return ids.map fun id => openRow (if nested then "local-" ++ mode else mode) stx id state'
NEW='''    if mode == "simple" then
      -- Lean.Elab.Open.elabOpenDecl resolves each operand after opening its predecessors.
      let mut current := state
      let mut rows := #[]
      for id in ids do
        let names := resolveOpen current id.getId
        rows := rows.push (openRow (if nested then "local-" ++ mode else mode) stx id current)
        let scope := current.scopes.head!
        let opened := names.foldl (fun acc ns => OpenDecl.simple ns [] :: acc) scope.openDecls
        current := { current with scopes := { scope with openDecls := opened } :: current.scopes.tail }
      return rows
    return ids.map fun id => openRow (if nested then "local-" ++ mode else mode) stx id state'''
def patched_helper(source):
 if source.count(OLD)!=1:raise ValueError('Shared collector changed: review the sequential-open adaptation before using it')
 return source.replace(OLD,NEW)
def collect(root,sources,output,lean=None):
 original=K.HERE
 with TemporaryDirectory(prefix='bulk-sequential-open-') as directory:
  private=Path(directory);(private/'klw1_collect_refs.lean').write_text(patched_helper((original/'klw1_collect_refs.lean').read_text()))
  try:
   K.HERE=private;K.collect(root,sources,output,lean)
  finally:K.HERE=original
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--root',type=Path,required=True);p.add_argument('--files',type=Path,required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--lean',type=Path);args=p.parse_args()
 collect(args.root,K.file_list(args.files),args.output,args.lean)
if __name__=='__main__':main()
