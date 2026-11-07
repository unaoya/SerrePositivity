# Ch 10 対応表確認結果（2026-11-07 JST）

対象は items.csv の Ch 10 全144項目。結果は [ch10.csv](../ch10.csv)。起点は main の 33ce6cfca。

判定は ok 89、fix 42、unsure 13。宣言の check は found 6、renamed 36、not_found 102。

| 訂正後の status | ok | fix | unsure |
| --- | ---: | ---: | ---: |
| own | 0 | 0 | 0 |
| mathlib | 0 | 3 | 0 |
| both | 0 | 0 | 0 |
| partial | 0 | 39 | 0 |
| none | 89 | 0 | 13 |

| 優先理由 | 対象 | fix | unsure | status 変更 |
| --- | ---: | ---: | ---: | ---: |
| A | 17 | 17 | 0 | 0 |
| B | 0 | 0 | 0 | 0 |
| C | 0 | 0 | 0 | 0 |
| D | 0 | 0 | 0 | 0 |

複数理由の項目はそれぞれの理由に計上。fix は名前空間や引用位置だけの訂正も含む。

## 主な訂正・照合結果

- 10.1.0.1（partial）Mathlib の単体・余単体対象は1圏版。自前の HasSmallGeometricRealizations は nerve Δᵒᵖ からの写像を直接量化するが、単体・余単体対象の定義は与えない。 [Kerodon](https://kerodon.net/tag/04QK)
- 10.1.1.9（partial）余単体 Kan 列の Reedy 条件下で、標準単体で重み付けした end を各段に持つ Tot がある。原文の任意の∞圏での余単体対象の極限という定義は未確認。 [Kerodon](https://kerodon.net/tag/04QZ)
- 10.1.2.28（partial）Mathlib の面と退化の合成恒等式は通常の単体的対象で確認。増強を含む作用素の族から単体的対象を再構成する逆向きは未確認。 [Kerodon](https://kerodon.net/tag/04S3)
- 10.1.6.7（partial）原文は追加退化からの鎖ホモトピーが退化部分複体を保ち、増強された正規化複体に降りる主張。ExtraDegeneracy は1圏での元の追加退化のデータ。 [Kerodon](https://kerodon.net/tag/04SF)
- 10.2.0.2（mathlib）原文は核対の余等化子で定義。Mathlib の IsRegularEpi と EffectiveEpi の同値、および核対の余等化子から RegularEpi を作る補題が比較を与える。 [Kerodon](https://kerodon.net/tag/04TP)
- 10.2.2.1（partial）Mathlib では一射の生成する sieve と、対応する余錐の余極限性による effective epimorphic の定義がある。原文の∞圏で生成された sieve の余錐による定義は未確認。 [Kerodon](https://kerodon.net/tag/04WH)

## 証拠と限界

- [原文の項目タグとページの SHA-256](ch10-source-index.json) は、Kerodon の各番号を実際の定理環境に対応付ける。
- [宣言の確認記録](ch10-kernel-evidence.json) は、段1・段1′の ID と補足の #check・#print axioms を区別する。補足は個別モジュールを共通ロック（--wait 1800）下で検査した。採用した引用で標準3公理以外を検出した項目は 0 件。
- [none の検索記録](ch10-none-search.jsonl) は、原文の語と節ごとの検索語で宣言名を検索し、Kerodon の番号引用を別に検索した。対象は SerrePositivity と固定版 Mathlib。順位は文字列探索の結果で、意味の一致を表さない。元表の否定理由と合わせて参照した。対応範囲を確定できない項目は unsure とした。
- check=not_found は最終引用が空欄という意味。未指定の宣言を Lean が拒否したことを表さない。

元表との番号・順序一致、重複なし、7列、採用した引用と型記録の対応を検証した。
