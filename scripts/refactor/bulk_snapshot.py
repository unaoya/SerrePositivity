#!/usr/bin/env python3
"""Render/compile the B2 verification-only v3b snapshot tool outside production Lean.
It retains ordinary private rows, records their real kernel names, and accepts raw
private-kernel rules that include the defining module. Expr DAG mixing, proof
erasure, axiom reachability and kernel attribute checks are unchanged.
Run --compile under the normal build lease. No existing shared source is edited.
"""
from pathlib import Path
import argparse,hashlib,json,subprocess,time
SOURCE_SHA256='5d466e25d7dfbda1b6e86515ee19b7c8e6f5ca6a2ad40945c3bbe8c19ebedcf8'
NATIVE = r'''
-- Verification-only companion for compiler-generated parser descriptor self IDs.
-- Ordinary kernel fingerprints below remain unchanged.
private def parserLiteralNat? (e : Expr) : Option Nat := do
  let e := e.consumeMData
  match e with
  | .lit (.natVal n) => return n
  | _ =>
    if e.isAppOfArity ``OfNat.ofNat 3 then
      match e.getAppArgs[1]!.consumeMData with
      | .lit (.natVal n) => return n
      | _ => none
    else none

private partial def parserLiteralName? (e : Expr) : Option Name := do
  let e := e.consumeMData
  if e.isConstOf ``Lean.Name.anonymous then return .anonymous
  let f := e.getAppFn
  let args := e.getAppArgs
  if (f.isConstOf ``Lean.Name.str || f.isConstOf ``Lean.Name.mkStr) && args.size == 2 then
    let p ← parserLiteralName? args[0]!
    let .lit (.strVal s) := args[1]!.consumeMData | none
    return .str p s
  if (f.isConstOf ``Lean.Name.num || f.isConstOf ``Lean.Name.mkNum) && args.size == 2 then
    let p ← parserLiteralName? args[0]!
    let n ← parserLiteralNat? args[1]!
    return .num p n
  let .const fn _ := f | none
  let ctorPrefix := "Lean.Name.mkStr"
  guard (fn.toString.startsWith ctorPrefix)
  let size ← (fn.toString.drop ctorPrefix.length).toString.toNat?
  guard (1 ≤ size && size ≤ 8 && args.size == size)
  args.foldlM (init := Name.anonymous) fun p a => do
    let .lit (.strVal s) := a.consumeMData | none
    return .str p s

'''
def add_parser_self_companion(source):
 anchor='private partial def exprDigest (rules : Rename)'
 assert source.count(anchor)==1
 source=source.replace(anchor,NATIVE+anchor)
 anchor='    for (field, stat) in [("type", some ty), ("body", body)] do'
 addition='''    let privateParserDescr := isPrivateName name && info.type.isConstOf ``Lean.ParserDescr
    let parserSelfBody : Option String ←
      if privateParserDescr then
        match info.value? (allowOpaque := true) with
        | none => pure none
        | some value =>
          let normalized := value.replace fun e =>
            if parserLiteralName? e == some name then some (toExpr `_snapshotParserSelf) else none
          if normalized == value then pure none
          else (fun stat => some (toString stat.1)) <$> fingerprint normalized
      else pure none
'''
 assert source.count(anchor)==1;source=source.replace(anchor,addition+anchor)
 anchor='("type_hash", toJson (toString ty.1)), ("body_hash", toJson (body.map fun x => toString x.1)),'
 assert source.count(anchor)==1;source=source.replace(anchor,anchor+'\n      ("private_parser_descr", toJson privateParserDescr), ("parser_self_body_hash", toJson parserSelfBody),')
 anchor='{ fileName := "<decl_snapshot>", fileMap := default }'
 assert source.count(anchor)==1;source=source.replace(anchor,'{ fileName := "<decl_snapshot>", fileMap := default, options := ({} : Options).set `maxHeartbeats (0 : Nat) }')
 source=source.replace('owned source-private references)','owned source-private references; parser-self-ID companion)')
 return source

def render(source):
 if hashlib.sha256(source.encode()).hexdigest()!=SOURCE_SHA256:raise ValueError('Shared snapshot source changed; review the private-owner adaptation')
 needle='    if isPrivateName name && parent == normalized then continue\n';assert source.count(needle)==1
 patched=source.replace(needle,'    -- B2 verification includes ordinary private declarations as well.\n')
 old='private def hashName (rename : Rename) (n : Name) : String :=\n  rename (canonicalName n)'
 new='''private def hashName (rename : Rename) (n : Name) : String :=
  if isPrivateName n then
    let raw := n.toString
    let owned := rename raw
    if owned != raw then owned else rename (canonicalName n)
  else rename (canonicalName n)'''
 assert patched.count(old)==1;patched=patched.replace(old,new).replace('(term-level, proof marker)','(term-level, proof marker; owned source-private references)')
 field='("name", toJson (canonicalName name)), ("parent", toJson parent.toString),';assert patched.count(field)==1
 return add_parser_self_companion(patched.replace(field,'("kernel_name", toJson name.toString), ("is_private", toJson (isPrivateName name)), '+field))
def main():
 parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--root',type=Path,required=True);parser.add_argument('--output-dir',type=Path,required=True);parser.add_argument('--compile',action='store_true');args=parser.parse_args();root=args.root.resolve();out=args.output_dir.resolve()
 if out.is_relative_to(root):raise ValueError('Verification source belongs outside the project worktree')
 source=root/'scripts/refactor/decl_snapshot.lean';generated=render(source.read_text());out.mkdir(parents=True,exist_ok=True);path=out/'Snapshot.lean'
 if path.exists() and path.read_text()!=generated:raise ValueError('Existing verification source differs; choose a fresh output directory')
 path.write_text(generated);receipt={'original_source_sha256':SOURCE_SHA256,'verification_source_sha256':hashlib.sha256(generated.encode()).hexdigest(),'compiled':False,'source':str(path)}
 if args.compile:
  steps=[]
  for command in [['lake','env','lean','--root='+str(out),'-c',str(out/'snapshot.c'),str(path)],['lake','env','leanc','-O3','-rdynamic','-o',str(out/'snapshot'),str(out/'snapshot.c')]]:
   start=time.monotonic();subprocess.run(command,cwd=root,check=True);steps.append({'command':command,'seconds':time.monotonic()-start})
  receipt.update(compiled=True,binary_sha256=hashlib.sha256((out/'snapshot').read_bytes()).hexdigest(),steps=steps,LEAN_SYSROOT=subprocess.check_output(['lake','env','lean','--print-prefix'],cwd=root,text=True).strip())
 (out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
if __name__=='__main__':main()
