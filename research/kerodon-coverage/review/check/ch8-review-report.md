# Ch 8 対応表確認結果（2026-11-07 JST）

対象は items.csv の Ch 8 全483項目。結果は [ch8.csv](../ch8.csv)。起点は main の 33ce6cfca。

判定は ok 344、fix 113、unsure 26。宣言の check は found 3、renamed 113、not_found 367。

| 訂正後の status | ok | fix | unsure |
| --- | ---: | ---: | ---: |
| own | 0 | 41 | 0 |
| mathlib | 2 | 4 | 0 |
| both | 0 | 0 | 0 |
| partial | 1 | 68 | 0 |
| none | 341 | 0 | 26 |

| 優先理由 | 対象 | fix | unsure | status 変更 |
| --- | ---: | ---: | ---: | ---: |
| A | 18 | 18 | 0 | 1 |
| B | 7 | 7 | 0 | 2 |
| C | 0 | 0 | 0 | 0 |
| D | 2 | 2 | 0 | 1 |

複数理由の項目はそれぞれの理由に計上。fix は名前空間や引用位置だけの訂正も含む。

## 主な訂正・照合結果

- 8.1.2.11（own）原文の指定した coslice inclusion の両端のファイバーへの制限は cosliceTwistedHomMap。単射性と圏同値を引用し、Kan 複体間の圏同値とホモトピー同値の比較を加えた。 [Kerodon](https://kerodon.net/tag/03K1)
- 8.3.3.13（partial）小さい quasicategory で構成された共変・反変の米田埋め込みは充満忠実。原文の局所小な任意の∞圏と指定された米田埋め込みの一般形は未確認。 [Kerodon](https://kerodon.net/tag/03NJ)
- 8.3.3.14（partial）小さい quasicategory で米田埋め込みは極限を保存。余米田の反映は逆圏側の別の主張。局所小一般の米田埋め込みについての両方向を直接は確認できない。 [Kerodon](https://kerodon.net/tag/03NP)
- 8.5.2.4（partial）Mathlib の定理は冪等完備性と等化子の存在の同値。証明は等化子側を使うが、原文は与えた個々の分裂の二本の射が等化子・余等化子を与える主張。 [Kerodon](https://kerodon.net/tag/03ZK)

## 証拠と限界

- [原文の項目タグとページの SHA-256](ch8-source-index.json) は、Kerodon の各番号を実際の定理環境に対応付ける。
- [宣言の確認記録](ch8-kernel-evidence.json) は、段1・段1′の ID と補足の #check・#print axioms を区別する。補足は個別モジュールを共通ロック（--wait 1800）下で検査した。採用した引用で標準3公理以外を検出した項目は 0 件。
- [none の検索記録](ch8-none-search.jsonl) は、原文の語、節の用語と別名、番号引用を使って SerrePositivity と固定版 Mathlib の宣言候補を絞ったもの。順位は文字列探索の結果で、意味の一致を表さない。元表の否定理由と合わせて参照した。対応範囲を確定できない項目は unsure とした。
- check=not_found は最終引用が空欄という意味。未指定の宣言を Lean が拒否したことを表さない。

元表との番号・順序一致、重複なし、7列、採用した引用と型記録の対応を検証した。

## やり直し（11-07、途中）

- §7 の基点は `81e593fb9`。旧 own・both・mathlib のうち 47/47 行を本文と採用型で照合した。
- 旧 none の行別検索は 219/367 行を記録した。残りはこれから確認する。

- §8.5 の旧 none を全件確認した。個別の冪等射の分裂、冪等完備化への前合成、準圏の圏における随伴を区別した。内アノダイン射の関手的分解では、頂点での全単射と高次単体までの全単射を分けて記録した。
