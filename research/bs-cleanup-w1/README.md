# BS の整理の段 0

基準は `cbcb40a59ae543edf4bacbeae3994a708bd56e2a`。比較の出発点は `ba24dceb6`。結論、保留、適用順は [報告](../../formalization-plans/stage-ii/consolidation/report-bs-cleanup.md)。

| 資料 | 読み方 |
| --- | --- |
| [items.csv](items.csv) | 指示書 §0 の32項目と同節が対象に含める BR26′。現在の状態、ソースの位置、11-12 からの差、分類。A は移動・改名、B は重複の一本化、C は証明の共用・言い換え、D は文書。 |
| [moves.csv](moves.csv) | 残る純移動案。IC-1 と同じ列。曖昧な型の置き換えが必要なものはここから外した。 |
| [signatures.csv](signatures.csv) | 既存のソース署名。宣言周辺の `variable` 行の候補を添えた。署名中に省略される section 引数と `include` は元ファイルで読める。 |
| [estimates.csv](estimates.csv) | 証明の作業量と前提。素の行数、補正係数 2 の区間、上端に 3% を加えた束ごとの外枠候補。 |
| [reachability.csv](reachability.csv)・[reachability-baseline.csv](reachability-baseline.csv) | BS の各ファイルから見た三根それぞれの到達経路。空欄はその根の集合から届かない。行数は改行の有無によらず物理行で数えた。 |
| [roots.json](roots.json) | 根の宣言・入口・正式監査、BS 内の対応表の根と根拠行、比較用の集計。 |
| [layers.csv](layers.csv) | 台帳と関連する節の旧 import 24 辺を現行の明示 import に照合。 |
| [impact.csv](impact.csv)・[coverage-impact.csv](coverage-impact.csv)・[branch-impact.json](branch-impact.json) | 現行コードの追従候補、対応表の直接参照、他レーンと IC-2 の照合。 |
| [docstrings.csv](docstrings.csv) | 先頭のモジュール文書に概要見出しがないファイルと、工程ラベルの候補行。 |

## 静的な数え方

- `git ls-tree` と `git cat-file` で各基準の追跡済みソースを読み、Archive を除く。import ヘッダーは IC-2 段 0 の `stage0.py`（`a1fbde1af`）のスキャナーで読み、`layer_check.imports` と照合した。`module`、`prelude`、`public/private/meta import`、`import all` を扱う。再帰は repo 内で解決した import に限る。
- 根1は root、`SerrePositivity/**/Entrypoints/` のファイル、`scripts/refactor/audit_sorries.lean` の4宣言の所在。根2は対応表の章 review の `own`・`partial`・`interface` のローカル宣言パス。列名に `_new` が付く表ではそちらを優先し、OE-W1 と IC-1 の旧パスを照合した。根3は正式監査一覧。監査ファイルのヘッダー外の読み込みは既存の `audit_imports.py` の字句規則で拾った。IC-2 の他枝からの到達は、今回の指示書では影響の資料として別に記録。
- 本体・blueprint・scripts・drafts の明示 import は別々に数える。推移的な影響は逆向きに閉包を取ったファイル数。型つき一覧の利用箇所はコメント・文字列を除いた識別子の末尾一致で、定義行を除く。監査命令や引用属性も文字列外の出現なら含める。短名の同名宣言を区別できない上限候補で、型から選ばれる暗黙の参照や Lean の生成宣言は採取していない。場所の追従件数は対応表のファイルと宣言の末尾名を併用した。
- 11-12 の review には旧パスの未解決が2,563参照ある。表の根由来の比較は当時の表から解決できた分。未解決の記載パスに `BhattScholze/` を含むものは0件。11-12 と現行とも正式監査の閉包だけで BS の全ファイルを覆うので、三根合併の閉包外の比較はこの欠落に左右されない。
- docstring は最初の `/-!` 内で `## 概要` の独立行を確認。文書コメントでは G 番号・G-A 系、B4 系、A1-b 系、F4〜F7、N3 の短い字句パターンで候補を出した。数学的記号と紛れる候補は一覧の文脈で読む。11-12 の監査と同一パターンであることは前提に置かない。
