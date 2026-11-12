"""2026-11-12 の宣言の場所の書き直し（B0）の判定。KL-W1 の改名表で名前と場所を引き直し、新しいファイルで宣言の行を照合する。
使い方：python3 refresh_locations.py <csv のルート> <改名表のディレクトリ> <出力 JSON> [--write]
--write なしなら表は変えず、解決・未解決の一覧だけを JSON に書く。"""
import csv,io,json,re,os,glob,sys,collections
root,T,out=sys.argv[1],sys.argv[2],sys.argv[3]; write='--write' in sys.argv
mm=json.load(open(os.path.join(T,'kl-module-map.json'))); nm=json.load(open(os.path.join(T,'kl-namespace-map.json')))
decl={r['old']:r['new'] for r in nm['rows'] if r['old']!=r['new']}
declmod={r['new']:r['new_module'] for r in nm['rows']}
DECL=re.compile(r'^\s*(?:@\[[^\]]*\]\s*)*(?:private |protected |noncomputable |nonrec |public |scoped |local )*(theorem|lemma|def|abbrev|structure|class|instance|inductive|opaque|axiom)\s+([A-Za-z0-9_.\'!?]+)')
cache={}
def index(path):
    if path in cache: return cache[path]
    d={}
    try:
        for i,l in enumerate(open(path,errors='ignore'),1):
            m=DECL.match(l)
            if m: d.setdefault(m.group(2).split('.')[-1],i); d.setdefault(m.group(2),i)
    except OSError: pass
    cache[path]=d; return d
stats=collections.Counter(); unresolved=[]; resolved=[]
def fix(entry,src):
    if ' @ ' not in entry: return entry
    name,loc=entry.split(' @ ',1); name=name.strip(); loc=loc.strip()
    path,_,line=loc.rpartition(':')
    if path.startswith('Mathlib/') or path.startswith('formalization-plans/'): stats['skip']+=1; return entry
    newname=decl.get(name,name)
    mod=path[:-5].replace('/','.') if path.endswith('.lean') else None
    newpath=path
    if mod and mod in mm: newpath=mm[mod].replace('.','/')+'.lean'
    if newname in declmod: newpath=declmod[newname].replace('.','/')+'.lean'
    short=newname.split('.')[-1]
    idx=index(newpath); ln=idx.get(newname) or idx.get(short)
    if ln is None and os.path.exists(path) and path!=newpath:
        idx2=index(path); ln2=idx2.get(name) or idx2.get(short)
        if ln2: newpath=path; ln=ln2; stats['kept old path']+=1
    if ln is None:
        stats['unresolved']+=1; unresolved.append({'source':src,'original':entry,'name':name,'path':path,'tried':newpath,'new_name':newname}); return entry
    stats['ok']+=1; resolved.append({'source':src,'original':entry,'new':f'{newname} @ {newpath}:{ln}'})
    return f'{newname} @ {newpath}:{ln}'
files=glob.glob(os.path.join(root,'*/review/ch*.csv'))+glob.glob(os.path.join(root,'*/items.csv'))+glob.glob(os.path.join(root,'k-coverage/*/*.csv'))
for f in sorted(files):
    raw=open(f,newline='').read(); nl='\r\n' if '\r\n' in raw else '\n'
    rows=list(csv.DictReader(io.StringIO(raw)))
    if not rows or 'declarations' not in rows[0]: continue
    key='number' if 'number' in rows[0] else ('item' if 'item' in rows[0] else None)
    ch=0
    for r in rows:
        src=f'{os.path.relpath(f,root)}:{r.get(key,"")}'
        parts=r['declarations'].split(' | '); new=[fix(p,src) for p in parts]
        if new!=parts: r['declarations']=' | '.join(new); ch+=1
    if write and ch:
        o=io.StringIO(); w=csv.DictWriter(o,list(rows[0].keys()),lineterminator=nl); w.writeheader(); w.writerows(rows); open(f,'w',newline='').write(o.getvalue())
json.dump({'stats':dict(stats),'unresolved':unresolved,'resolved':resolved},open(out,'w'),ensure_ascii=False,indent=1)
print(dict(stats))
