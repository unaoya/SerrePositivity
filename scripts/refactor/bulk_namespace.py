#!/usr/bin/env python3
"""Use exact unchanged namespace bindings for a plain multi-binding open.
Existing shared files are never edited. Other ambiguous opens retain review guards.
"""
from pathlib import Path
import os,sys,inspect
HERE=Path(__file__).resolve().parent
sys.path.insert(0,os.environ.get('BULK_REFACTOR_TOOLS',str(HERE)))
import klw1_namespace as K
OLD='''            if len(set(new_names)) != 1 or (mode.startswith("local-") and
                                           written.removeprefix("_root_.") not in names):'''
NEW='''            if mode == "simple" and len(set(new_names)) > 1 and new_names == names:
                # Preserve every actual original binding in its original order.
                # Explicit roots avoid capture by a newly moved enclosing namespace.
                edit(row, " ".join("_root_." + name for name in new_names))
                continue
            if len(set(new_names)) != 1 or (mode.startswith("local-") and
                                           written.removeprefix("_root_.") not in names):'''
def adapted_rewrite():
 source=inspect.getsource(K.rewrite)
 if source.count(OLD)!=1:raise ValueError('Shared rewriter changed: review the plain-open adaptation')
 scope=dict(vars(K));exec(compile(source.replace(OLD,NEW),'<bulk plain-open rewriter>','exec'),scope)
 return scope['rewrite']
rewrite=adapted_rewrite()
def main():
 if len(sys.argv)>1 and sys.argv[1]=='collect':
  import bulk_collect
  sys.argv.pop(1)
  return bulk_collect.main()
 original=K.rewrite
 try:
  K.rewrite=rewrite
  return K.main()
 finally:K.rewrite=original
if __name__=='__main__':raise SystemExit(main())
