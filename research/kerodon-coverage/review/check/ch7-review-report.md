# Ch 7 対応表確認結果（2026-11-07 JST）

対象は items.csv の Ch 7 全519項目。結果は [ch7.csv](../ch7.csv)。起点は main の 33ce6cfca。

判定は ok 187、fix 245、unsure 87。宣言の check は found 12、renamed 241、not_found 266。

| 訂正後の status | ok | fix | unsure |
| --- | ---: | ---: | ---: |
| own | 0 | 88 | 0 |
| mathlib | 1 | 2 | 0 |
| both | 0 | 0 | 0 |
| partial | 7 | 155 | 0 |
| none | 179 | 0 | 87 |

| 優先理由 | 対象 | fix | unsure | status 変更 |
| --- | ---: | ---: | ---: | ---: |
| A | 35 | 35 | 0 | 2 |
| B | 6 | 6 | 0 | 0 |
| C | 20 | 2 | 1 | 2 |
| D | 5 | 5 | 0 | 0 |

複数理由の項目はそれぞれの理由に計上。fix は名前空間や引用位置だけの訂正も含む。

## 主な訂正・照合結果

- 7.1.8.4（partial）Mathlib の積圏の図式に対する余極限の Fubini 同型を追加。両添字圏の全余極限と外側の余極限を仮定し、各点の余極限だけから始める∞圏版は未確認。 [Kerodon](https://kerodon.net/tag/06A2)
- 7.1.8.5（partial）原文は二段の余極限の Fubini 公式。Mathlib に1圏での余極限の比較同型がある。自前の番号引用は関手圏の各点極限判定で、原文の公式とは結論が異なる。 [Kerodon](https://kerodon.net/tag/06A3)
- 7.4.1.18（partial）引用は U と pointed space での切断の制限が同値になる条件を比較する。指定した境界からの相対極限持ち上げの存在と、任意の持ち上げの相対極限性は引用型に現れない。 [Kerodon](https://kerodon.net/tag/06MF)
- 7.5.6.1（partial）[ModelCategory C] と生成系を使う一般の射影モデル構造。原文の SSet には本体の ModelCategory instance なし。単体的集合の図式の持ち上げによる定義は未確認。 [Kerodon](https://kerodon.net/tag/03C4)
- 7.6.5.11（own）Kan ファイブレーションの塔の極限の Kan 性と、空間圏での極限錐の結果を確認。初段射影の補題に加えて limit_kanComplex を明示した。 [Kerodon](https://kerodon.net/tag/03HU)

## 証拠と限界

- [原文の項目タグとページの SHA-256](ch7-source-index.json) は、Kerodon の各番号を実際の定理環境に対応付ける。
- [宣言の確認記録](ch7-kernel-evidence.json) は、段1・段1′の ID と補足の #check・#print axioms を区別する。補足は個別モジュールを共通ロック（--wait 1800）下で検査した。採用した引用で標準3公理以外を検出した項目は 0 件。
- [none の検索記録](ch7-none-search.jsonl) は、原文の語、節の用語と別名、番号引用を使って SerrePositivity と固定版 Mathlib の宣言候補を絞ったもの。順位は文字列探索の結果で、意味の一致を表さない。元表の否定理由と合わせて参照した。対応範囲を確定できない項目は unsure とした。
- check=not_found は最終引用が空欄という意味。未指定の宣言を Lean が拒否したことを表さない。
- [モデル圏 instance の記録](ch7-model-instance.json) では、Quillen の余ファイブレーション・ファイブレーション構造は合成でき、ModelCategory SSet は合成できなかった。一般の ModelCategory 仮定が残る 6 項目を partial とした。

元表との番号・順序一致、重複なし、7列、採用した引用と型記録の対応を検証した。

## やり直し（11-07、途中）

- §7 の基点は `81e593fb9`。旧 own・both・mathlib のうち 91/91 行を本文と採用型で照合した。
- 旧 none の行別検索は 136/266 行を記録した。残りはこれから確認する。
- §7.1–§7.4 の行別検索を記録。原典の引用索引（9,711件）と現行 Lean docstring を照合した。部分対応に改めた41行の型・公理検査はロックを通した。残りの unsure は63行。
- 7.3.6.1 の LeftKanHomUniversal は h Fun の Hom 集合での全単射。Kerodon の Kan 複体のホモトピー同値より結論が弱い。
