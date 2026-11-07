# Ch 4 対応表確認結果（2026-11-07 JST）

対象は items.csv の Ch 4 全 588 項目。結果は [章 CSV](../ch4.csv)。確認用の Lean コマンドは既存宣言の型・公理・instance を調べるものに限った。

判定は ok 322 件、fix 265 件、unsure 1 件。check は found 41 件、renamed 260 件、not_found 287 件。

## 判定の内訳

| 元の status | ok | fix | unsure |
| --- | ---: | ---: | ---: |
| own | 0 | 124 | 0 |
| mathlib | 30 | 12 | 1 |
| both | 0 | 1 | 0 |
| partial | 8 | 122 | 0 |
| none | 284 | 6 | 0 |

| 優先理由 | 対象 | fix | fix の率 | status 訂正 | unsure |
| --- | ---: | ---: | ---: | ---: | ---: |
| A | 28 | 24 | 85.7% | 4 | 1 |
| B | 11 | 9 | 81.8% | 1 | 0 |
| C | 31 | 2 | 6.5% | 2 | 0 |
| D | 8 | 6 | 75.0% | 0 | 0 |

fix は名前空間・出典・引用の訂正も含む。主張の範囲の変更を見るときは status 訂正列を参照。unsure の status は暫定値。

## 主な訂正

- 4.1.1.1 は Mathlib の InnerFibration が定義に対応し、元表の both を mathlib に訂正。
- 4.3.2.9 の原文は join の包含から slice・coslice への一意な因子化。充満忠実性の引用を除外。
- 4.4.2.6 に初期ホーンでの可逆性判定を追加。
- 4.9.1.16 は整列集合の比較可能性から順序同型の一意性へ引用を変更。

## 確認範囲と証拠

- [ch4-evidence.json](ch4-evidence.json) に本文の項目タグと節ページの SHA-256、段1・段1′の記載 ID、探索語、番号のヒット、候補の宣言名と位置を記録した。
- [ch4-kernel-evidence.json](ch4-kernel-evidence.json) に段1・段1′の集計から採用できなかった追加候補の Lean 出力と、既存集計から再利用した ID を記録した。既にビルド済みのモジュールを読み込み、指定の --wait 1800 のロックを使用した。
- check=not_found は対応宣言を採用しなかった行。元の欄が空の場合は、候補探索の結果を表す。check=renamed は名前補正と新たな引用の検査を含む。
- 「なし」は SerrePositivity と固定版 Mathlib の宣言見出し・周辺コメント・番号を探索した範囲の判定。語による順位付けは同義語のすべてを網羅するものではない。
- 所定の 7 列、元表と同一の番号・順序、重複なし、採用した引用と検査結果の対応を確認。標準3公理以外を含む採用行は 0 件。

## 未確定

- 4.9.1.27 — 引用は最小濃度の共終部分集合と、整列性を仮定した順序型の式。任意の線形順序で整列な共終部分集合を作る宣言は未確定。

## やり直し（11-07）

§7 の対象として、前回の own・both・mathlib 157 件と、none 287 件、unsure 1 件を再照合した。
採用した宣言の型は [kernel の記録](ch4-kernel-evidence.json) の `depth_review`、none の番号・タグ、対語を含む型検索、同小節の近接宣言は [行ごとの検索記録](ch4-none-search.json) に置いた。
`citations.csv` が作業木にないため、引用は `citations-summary.md` とソースのコメントから再抽出した。小節内に own・both の採用先がない行は、近傍を選ぶ代替の起点を検索記録に明記した。

| status | 件数 |
| --- | ---: |
| own | 96 |
| both | 0 |
| mathlib | 35 |
| partial | 172 |
| none | 285 |

ok 314 件、fix 274 件、unsure 0 件。

- 4.4.1.8 は own。仮定：∞ 圏間の F（Lean が弱い：EquivalenceLifting.op 自体は任意の単体集合間で成り立つ）。結論：EquivalenceLifting は ∞ 圏上では内ファイブレーションと同値辺持ち上げの組。反転で保たれ、二重反転が恒等なので反対方向にも保たれる（一致）。
- 4.8.4.5 は partial。仮定：∞ 圏間の内ファイブレーション（Lean が強い：正次元の一方向は F の充満忠実性を仮定）。結論：全ての正次元の境界充填と充満忠実性の対応を確認。単一の n での n-full との同値や n=0 の isofibration 版は未確認（Lean が弱い）。

前回からの status の変更は mathlib → partial が 6 件、none → own が 1 件、none → partial が 1 件、own → partial が 21 件。
