#!/usr/bin/env python3
"""R79: rewrite archived planning links inside module docstrings; dry-run by default.
No Lean/build/git commands. DG sources are never selected. Apply only in the approved bundle.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import sys

from lean_source import read_source, write_source

ROOT=Path(__file__).resolve().parents[2]
OLD={'plan':'formalization-plans/k-theory.md',
     'inventory':'formalization-plans/k-theory-generalization-inventory.md'}
ARROWS={'SerrePositivity/CategoryTheory/'+s+'.lean' for s in
        ('ArrowFactorization','ArrowFactorizationCategory','ArrowFactorizationTransport')}
DOCS='https://docs.github.com/en/get-started/writing-on-github/getting-started-with-writing-and-formatting-on-github/basic-writing-and-formatting-syntax'


def github_slug(heading):
    # Plain heading rule: lowercase, spaces -> hyphens, remove punctuation
    # other than hyphens/underscores. The §396 heading has no inline markup.
    return re.sub(r'[^\w\- ]','',heading.lower()).replace(' ','-')


def section_anchor(text):
    seen=set();matches=[]
    for heading in re.findall(r'^#{1,6} +(.+?) *#*$',text,re.M):
        base=github_slug(heading);anchor=base;i=0
        while anchor in seen:i+=1;anchor=base+'-'+str(i)
        seen.add(anchor)
        if re.match(r'^396\. ',heading):matches.append((heading,anchor))
    if len(matches)!=1:raise ValueError('expected exactly one §396 archive heading')
    return matches[0]


def doc_ranges(text):
    """Locate /-! comments, respecting strings, line comments and nested blocks."""
    spans=[];i=0
    while i<len(text):
        if text.startswith('--',i):
            end=text.find('\n',i);i=len(text) if end<0 else end+1
        elif text[i]=='"':
            i+=1
            while i<len(text):
                if text[i]=='\\':i+=2
                elif text[i]=='"':i+=1;break
                else:i+=1
        elif text.startswith('/-',i):
            start=i;doc=text.startswith('/-!',i);depth=1;i+=2
            while i<len(text) and depth:
                if text.startswith('/-',i):depth+=1;i+=2
                elif text.startswith('-/',i):depth-=1;i+=2
                else:i+=1
            if depth:raise ValueError('unclosed comment')
            if doc:spans.append((start,i))
        else:i+=1
    return spans


def rewrite(text,path,document,anchor):
    spans=doc_ranges(text);edits=[]
    for kind in ('plan','inventory') if document=='all' else (document,):
        for match in re.finditer(re.escape(OLD[kind]),text):
            if not any(a<=match.start()<match.end()<=b for a,b in spans):
                raise ValueError('reference outside module docstring: '+path)
            line_start=text.rfind('\n',0,match.start())+1
            prefix=text[line_start:match.start()]
            label='reference' if re.match(r'^\s*\['+('plan' if kind=='plan' else 'inventory')+r'\]:',prefix) else 'inline'
            if kind=='plan' and label=='inline' and path!='SerrePositivity/Spectra/StageTwo.lean':
                raise ValueError('unreviewed inline plan reference: '+path)
            if kind=='plan' and text[match.end():].startswith('#'):
                raise ValueError('unexpected existing plan anchor: '+path)
            replacement=('formalization-plans/archive/k-theory-v1.md#'+anchor if kind=='plan'
                         else 'formalization-plans/archive/k-theory-generalization-inventory.md')
            edits.append({'start':match.start(),'end':match.end(),'replacement':replacement,
                          'document':kind,'form':label,'line':text.count('\n',0,match.start())+1})
    after=text
    for e in sorted(edits,key=lambda x:x['start'],reverse=True):
        after=after[:e['start']]+e['replacement']+after[e['end']:]
    return after,edits


def plan(root,document='all'):
    archive=root/'formalization-plans/archive/k-theory-v1.md'
    heading,anchor=section_anchor(read_source(archive))
    if not (root/'formalization-plans/archive/k-theory-generalization-inventory.md').is_file():
        raise ValueError('inventory archive missing')
    changes=[];counts=Counter()
    for area in ('CategoryTheory','HomotopicalAlgebra','Spectra'):
        for path in sorted((root/'SerrePositivity'/area).rglob('*.lean')):
            before=read_source(path);rel=path.relative_to(root).as_posix()
            after,edits=rewrite(before,rel,document,anchor)
            if not edits:continue
            for e in edits:counts[e['document']+'_'+e['form']]+=1
            changes.append({'path':rel,'sha256':hashlib.sha256(before.encode()).hexdigest(),
                            'before':before,'after':after,'edits':edits})
    expected={'plan_reference':618,'plan_inline':1,'inventory_reference':618,'inventory_inline':16}
    expected={k:v for k,v in expected.items() if document=='all' or k.startswith(document+'_')}
    arrows=sorted(ARROWS & {c['path'] for c in changes})
    report={'status':'PASS' if dict(counts)==expected else 'STOP','mode':'DRY RUN','document':document,
            'heading':heading,'anchor':anchor,'expected':expected,'counts':dict(counts),
            'files':len(changes),'arrow_files':arrows,'excluded_area':'SerrePositivity/DifferentialGraded',
            'changes':[{k:v for k,v in c.items() if k not in ('before','after')} for c in changes]}
    if document=='all' and len(arrows)!=3:report['status']='STOP'
    return report,changes


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--root',type=Path,default=ROOT)
    p.add_argument('--document',choices=['plan','inventory','all'],default='all')
    group=p.add_mutually_exclusive_group();group.add_argument('--dry-run',action='store_true');group.add_argument('--apply',action='store_true')
    p.add_argument('--output',type=Path)
    args=p.parse_args()
    try:
        report,changes=plan(args.root,args.document)
        if args.apply and report['status']=='PASS':
            if args.document=='all':raise ValueError('apply one document per commit: --document plan or inventory')
            for c in changes:
                if read_source(args.root/c['path'])!=c['before']:raise ValueError('source changed: '+c['path'])
            for c in changes:write_source(args.root/c['path'],c['after'])
            report['mode']='APPLIED'
        text=json.dumps(report,ensure_ascii=False,indent=2)+'\n'
        if args.output:args.output.write_text(text)
        print(json.dumps({k:v for k,v in report.items() if k!='changes'},ensure_ascii=False,indent=2))
        return int(report['status']!='PASS')
    except (OSError,ValueError) as exc:
        print('rewrite_r79_docs: STOP: '+str(exc),file=sys.stderr);return 1

if __name__=='__main__':sys.exit(main())
