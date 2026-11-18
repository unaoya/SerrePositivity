"""追加choose候補のソース利用箇所索引と段0判定。適用はしない。"""
from pathlib import Path
import json,re,csv,collections,subprocess
ROOT=Path(__file__).resolve().parents[2];OUT=Path(__file__).resolve().parent
raw=json.loads((OUT/'choose-new-candidates.json').read_text());data=[r for r in raw['definitions'] if r['kind'] in ('def','abbrev','instance')]
# Raw source excerpts are reproducible from committed source SHA; keep capture outside git.
if any('original_source' in r for r in raw['definitions']):Path('/private/tmp/ic-w1-choose-capture.json').write_text(json.dumps(raw,ensure_ascii=False))
lanes=json.loads((OUT/'branch-impact.json').read_text())
for r in data:r['other_lanes']=[b for b,l in lanes.items() if r['file'] in l['touched_paths']]
names={r['source_name'].split('.')[-1] for r in data};usage=collections.defaultdict(list);counts=collections.Counter()
pat=re.compile(r'(?<![\w\u0080-\uffff])('+'|'.join(re.escape(n) for n in sorted(names,key=len,reverse=True))+r')(?![\w\u0080-\uffff])')
paths=subprocess.check_output(['git','ls-files','SerrePositivity/*.lean','SerrePositivity/**/*.lean'],cwd=ROOT,text=True).splitlines()
for p in paths:
 f=ROOT/p
 if not f.exists():continue
 for line,s in enumerate(f.read_text().splitlines(),1):
  for name in {m[1] for m in pat.finditer(s)}:
   counts[name]+=1
   # collect compact evidence, actual binding needs compiler next morning
   if len(usage[name])<30:usage[name].append({'path':p,'line':line,'text':s.strip()[:650]})
manual={
'ICCH108':('要らない','存在命題自体が f = eqToHom h を指定し、同ファイルの chosenEqToHom_eq が回収する。一意の指定射。'),
'ICCH083':('不明','CofiberSquareFamily の span/colimit の族を選ぶ。forgetとの一致は回収するが、任意の指定pushout/coconeとの族としての一致まで存在命題に含むか、利用側のExact functorと照合が要る。'),
'ICCH467':('不明','StrictSemifreeColimitFamily の forget/evaluation 一致は高次単体でも回収する。後の指定 derived coconeとの比較・単位までこの存在命題だけで十分か未確定。'),
'ICCH127':('不明','GeneralLocalization は局所化の普遍性だけから対象を選び、edgeLocalizationMapと同じ証拠を使う。指定hammock/coherent nerve模型との同一性は別比較を要するため不明。'),
'ICCH128':('不明','edgeLocalizationと同じ存在証拠のchoose_specから射を選ぶ。固定した指定局所化射との比較条件は存在だけでは決まらない。'),
'ICCH499':('要らない','NormalizationCompositionTetrahedron の存在命題は同じ normalization の辺・面を固定した充填を選ぶ。利用側はこの同じ充填の面等式を回収しており、別の指定充填との等式を追加要求しない。'),
'ICCH519':('要らない','FactorZeroObjects で同じ選択の zero_spec を回収し、利用側は選んだ零対象の消滅性を使用する。任意の元から選んだ零対象との定義的等号は要求しない。'),
'ICCH520':('要らない','ZeroObject で同じ選択証拠から代表加群の零との同型を回収する。零対象性と同型による移送を使う経路であり、別の固定代表との等号は要求しない。'),
'ICCH521':('要らない','dgGluingZeroObjectと同じexistsのchoose_specから同型を選ぶ。chosen objectと同型の対応は同じ証拠に固定されている。'),
'ICCH560':('要らない','TruncatedConeNormalizeNext は退化表示の存在からi,yを選ぶが、同ファイルの退化上の値の補題で標準退化と一致させる。後続はその等式を使用する。'),
}
for r in data:
 n=r['source_name'].split('.')[-1];s='\n'.join(r['selection_lines'])
 numeric=(not re.search(r'Classical\.(?:choose|choice)|exists|nonempty',s) and bool(re.search(r'(?:Nat\.choose|\b\w+\.choose\s+2)',s)))
 r['category']='二項係数（除外）' if numeric else ('固定比較射の逆・同値候補' if re.search(r'isQCatEquivalence|IsQCatEquivalence|_equivalence|QCatEquivalence',s) else '存在証拠からのデータ候補')
 r['compatibility'],r['reason']=manual.get(r['id'],('対象外','Nat.choose/自然数.choose は選択公理のchooseではない。') if numeric else ('不明','短名の利用箇所を採取した。静的な短名一致では別の指定構成との追加の一致要求・束縛を全て確定できないため、要らないへ自動判定しない。'))
 r['remedy']='変更なし' if r['compatibility'] in ('要らない','対象外') else '同名・同型・同仮定を保ち、利用側の指定対象/射/単位との一致を含む証拠から選び直す案。必要な両立が同じ仮定で示せなければ改変せず保留。'
 r['consumer_occurrences']=counts[n]
 # prefer other files; preserve same file laws too
 r['consumer_evidence']=sorted(usage[n],key=lambda x:x['path']==r['file'])[:6]
 r['consumer_note']='文字列索引。generic短名・open・コメントの一致を含み得る。native参照の証明ではない。'
 r['existence_evidence']=r['existence_references'] or r['selection_lines']
 r.pop('original_source',None)
(OUT/'choose-additional-review.json').write_text(json.dumps({'definitions':data,'summary':dict(collections.Counter(r['compatibility'] for r in data))},ensure_ascii=False,indent=2)+'\n')
with (OUT/'choose-additional.md').open('w') as f:
 f.write('# BR55 追加データ候補（ソース静的分析）\n\n全選択語の候補から証明専用を除いた表。短名はkernel名ではない。利用側の全文索引と判定理由は choose-additional-review.json。\n\n|ID|宣言・ファイル:行|選択元（ソース）|両立|処置|推移importer|他レーン|\n|---|---|---|---|---|---:|---|\n')
 for r in data:
  proof=' / '.join(r['existence_evidence']).replace('|','\\|').replace('\n',' ')[:900]
  f.write(f"|{r['id']}|`{r['source_name']}` — `{r['file']}:{r['line']}`|`{proof}`|{r['compatibility']}：{r['reason']}|{r['remedy']}|{r['transitive_importers']}|{','.join(r['other_lanes']) or 'なし（変更ファイル集合との照合）'}|\n")
# trim raw candidate source blobs in committed inventory; capture path above retains source excerpts.
for r in raw['definitions']:r.pop('original_source',None)
(OUT/'choose-new-candidates.json').write_text(json.dumps(raw,ensure_ascii=False,indent=2)+'\n')
print(collections.Counter(r['compatibility'] for r in data));print(collections.Counter(r['category'] for r in data))
