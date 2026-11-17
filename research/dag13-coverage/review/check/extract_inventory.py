#!/usr/bin/env python3
"""Re-extract numbered environments from the pinned PDF; no Lean or network use.
Requires pdftotext. Compare labels, page/line positions, section ranges and kinds.
Do not write the copyrighted PDF/text into the repository.
"""
import argparse,csv,hashlib,json,re,shutil,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4]
KINDS='Definition|Theorem|Lemma|Proposition|Corollary|Remark|Example|Construction|Notation|Warning|Question|Conjecture|Convention|Observation|Terminology|Variant'

def inventory(s,book):
    if book=='ns':
        # At PDF p.24, the label precedes “Definition” in pdftotext's reading order.
        s=s.replace('           I.3.7. Let SpBG\nDefinition L','Definition I.3.7. Let SpBG\nL')
    number=r'\d+\.\d+\.\d+' if book=='dag13' else r'(?:[IV]+\.\d+\.\d+|[ABC]\.\d+|1\.[1-7])'
    pat=re.compile(r'^[ \f]*(?P<kind>'+KINDS+r')\s+(?P<number>'+number+r')(?=[. (\n])(?P<tail>[^\n]*)',re.M)
    starts={m[1]:m.start() for m in re.finditer(r'^([123](?:\.[1-6])?) +[A-ZpE]',s,re.M)} if book=='dag13' else {}
    items={}
    for m in pat.finditer(s):
        n=m['number'];tail=m['tail']
        section=n.rsplit('.',1)[0] if book=='dag13' or n[0].isalpha() else 'Introduction'
        if book=='dag13' and m.start()<starts.get(section,starts.get(n[0],0)):continue
        if not (tail.startswith('.') or tail.startswith(' (')):continue
        # In-proof references and repeated statements never add another row.
        if n not in items:
            items[n]=dict(number=n,kind=m['kind'],section=section,pdf_page=str(s[:m.start('kind')].count('\f')+1),layout_line=str(s[:m.start()].count('\n')+1))
    return items

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--book',choices=['dag13','ns'],required=True);p.add_argument('--pdf',type=Path,required=True)
    a=p.parse_args();folder=ROOT/'research'/f'{a.book}-coverage'
    meta=json.loads((folder/'review/check/edition.json').read_text())
    assert hashlib.sha256(a.pdf.read_bytes()).hexdigest()==meta['sha'],'PDF edition/hash mismatch'
    exe=shutil.which('pdftotext') or '/opt/homebrew/bin/pdftotext'
    s=subprocess.check_output([exe,'-layout',str(a.pdf),'-'],text=True)
    actual=inventory(s,a.book)
    with (folder/'review/check/source-items.csv').open() as f:expected={r['number']:r for r in csv.DictReader(f)}
    assert actual==expected,{'added':list(actual.keys()-expected.keys()),'missing':list(expected.keys()-actual.keys()),'different':[n for n in actual.keys()&expected.keys() if actual[n]!=expected[n]]}
    assert len(actual)==meta['count']
    print(f'{a.book}: {len(actual)} labels, kinds, sections, PDF pages and layout lines match pinned PDF')
if __name__=='__main__':main()
