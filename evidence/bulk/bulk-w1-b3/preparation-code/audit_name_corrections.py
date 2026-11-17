"""Exact audit-data corrections derived from frozen declared names, never live output."""
from pathlib import Path
import json,re
W=Path('/tmp/bulk-w1-b3')
def apply(path,payload):
 ledger=json.load(open(W/'audit-declaration-name-corrections.json'));fixes=[x for x in ledger['fixes'] if x['path']==path]
 if not fixes:return payload
 text=payload.decode();marker='-- EInfinity の全宣言の推移的な公理依存を監査する。';assert marker in text;prefix,tail=text.split(marker,1)
 for fix in fixes:
  before=fix['wrong_module_literal'];after=fix['correct_declaration_literal'];pattern=re.compile(r'(?<![\w.`])'+re.escape(before)+r'(?![\w.])');matches=list(pattern.finditer(prefix));assert len(matches)==fix['expected_occurrences'],(path,before,len(matches));assert not pattern.search(tail)
  for match in matches:
   start=prefix.rfind('private def e2RequiredBatch',0,match.start());assert start>=0 and 'Array Lean.Name :=' in prefix[start:match.start()]
  prefix=pattern.sub(lambda _:after,prefix)
 return (prefix+marker+tail).encode()
