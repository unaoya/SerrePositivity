# Ch 9 対応表確認結果（2026-11-07 JST）

対象は items.csv の Ch 9 全597項目。結果は [ch9.csv](../ch9.csv)。起点は main の 33ce6cfca。

判定は ok 273、fix 260、unsure 64。宣言の check は found 17、renamed 258、not_found 322。

| 訂正後の status | ok | fix | unsure |
| --- | ---: | ---: | ---: |
| own | 0 | 40 | 0 |
| mathlib | 3 | 3 | 0 |
| both | 0 | 0 | 0 |
| partial | 12 | 163 | 0 |
| none | 258 | 54 | 64 |

| 優先理由 | 対象 | fix | unsure | status 変更 |
| --- | ---: | ---: | ---: | ---: |
| A | 39 | 36 | 1 | 3 |
| B | 20 | 18 | 0 | 1 |
| C | 0 | 0 | 0 | 0 |
| D | 3 | 3 | 0 | 3 |

複数理由の項目はそれぞれの理由に計上。fix は名前空間や引用位置だけの訂正も含む。

## 主な訂正・照合結果

- 9.1.6.4（partial）厳密 filtered Kan 余錐の台が余極限なら native 空間圏でも余極限という宣言を追加。原文は coherent nerve への包含を指定する。補助引用は [ModelCategory C] を仮定し SSet に本体の instance なし。 [Kerodon](https://kerodon.net/tag/03DH)
- 9.1.8.7（partial）右 cofinal な κ-directed poset の存在は確認。κ◁λ と C の λ-small 性から、添字 poset も λ-small に取る原文の基数評価は引用型にない。 [Kerodon](https://kerodon.net/tag/02QA)
- 9.3.4.23（none）原文は κ-flat 関手が存在する κ-small 極限をすべて保つという主張。引用は Ind 頂点の判定で、極限の保存を結論しない。保存の該当宣言は未確定。 [Kerodon](https://kerodon.net/tag/0662)
- 9.4.0.1（mathlib）原文は通常の圏の accessible 性。Mathlib の IsAccessibleCategory と IsCardinalAccessibleCategory が対応し、自前の quasicategory 用 IsKappaAccessible はこの1圏の項目の重複から外す。 [Kerodon](https://kerodon.net/tag/06GU)
- 9.5.0.1（mathlib）原文は完全束で任意の部分集合に上限が存在する主張。inf から完全束を作る構成を、任意の集合の sSup が IsLUB である定理へ差し替えた。 [Kerodon](https://kerodon.net/tag/06PT)

## 証拠と限界

- [原文の項目タグとページの SHA-256](ch9-source-index.json) は、Kerodon の各番号を実際の定理環境に対応付ける。
- [宣言の確認記録](ch9-kernel-evidence.json) は、段1・段1′の ID と補足の #check・#print axioms を区別する。補足は個別モジュールを共通ロック（--wait 1800）下で検査した。採用した引用で標準3公理以外を検出した項目は 0 件。
- [none の検索記録](ch9-none-search.jsonl) は、原文の語、節の用語と別名、番号引用を使って SerrePositivity と固定版 Mathlib の宣言候補を絞ったもの。順位は文字列探索の結果で、意味の一致を表さない。元表の否定理由と合わせて参照した。対応範囲を確定できない項目は unsure とした。
- check=not_found は最終引用が空欄という意味。未指定の宣言を Lean が拒否したことを表さない。
- [モデル圏 instance の記録](ch9-model-instance.json) では、Quillen の余ファイブレーション・ファイブレーション構造は合成でき、ModelCategory SSet は合成できなかった。一般の ModelCategory 仮定が残る 5 項目を partial とした。

元表との番号・順序一致、重複なし、7列、採用した引用と型記録の対応を検証した。

## やり直し（11-07、途中）

- §7 の基点は `81e593fb9`。旧 own・both・mathlib のうち 46/46 行を本文と採用型で照合した。
- 旧 none の行別検索は 52/376 行を記録した。残りはこれから確認する。
