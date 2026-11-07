# Ch 3 — Kerodon 対応表の照合

- 対象は Ch 3 全 339 行。優先対象 58 行の内訳は ok 20、fix 38。
- Kerodon 本文と Lean の型を照合し、最終引用に含む 230 種の宣言・ソースの組について `#check` と `#print axioms` の出力を確認した。このうち 41 種はこの章のために追加検査した。標準 3 公理を超える依存は 0。型にモデル圏の仮定がある 2 種は下記のとおり。
- 段 3 の記録は元の none または最終判定が none の 185 行。最終判定は none 153、partial 31、own 1。作業木に `citations.csv` が見つからなかったため、`citations-summary.md` を参照し、現行 Lean ソースに対して項目番号、同じ小節の番号、タグ URL を直接検索した。検索語、検索範囲、候補と採否は `ch3-none-search.json`。
- `check` は最終引用に対する記録。元のまま型を確認した found 11、名称または引用先を更新して型を確認した renamed 175、最終引用を採らなかった not_found 153。

| 最終 status | ok | fix | unsure | 合計 |
|---|---:|---:|---:|---:|
| own | 0 | 48 | 0 | 48 |
| both | 0 | 0 | 0 | 0 |
| mathlib | 1 | 16 | 0 | 17 |
| partial | 5 | 115 | 1 | 121 |
| none | 150 | 3 | 0 | 153 |
| 計 | 156 | 182 | 1 | 339 |

- `PointedObject.cofiber` と商射の型で、任意の単体集合の対の商を終対象への押し出しとして作る構成を確認した。 [3.2.2.1](https://kerodon.net/tag/00VK)
- `filteredColimitMap_isWeakHomotopyEquivalence_of_pointwise` は小さい filtered 圏上の任意の単体集合値図式を扱い、各成分が弱ホモトピー同値なら余極限の写像も弱ホモトピー同値となる。 [3.2.8.3](https://kerodon.net/tag/00XE)
- Mathlib の幾何学的実現と特異単体集合の随伴を確認した。Milnor の単位・余単位の弱ホモトピー同値性と、弱同値を反転した圏の同値は partial とした。 [3.6.4.1](https://kerodon.net/tag/0142)、[3.6.4.2](https://kerodon.net/tag/0143)
- 3.3.7.7 の候補は `[ModelCategory SSet]` と fibration のクラスの等式を要求する。該当モジュールで `#synth ModelCategory SSet` が失敗したため、§6.1 に従い partial・unsure とした。 [3.3.7.7](https://kerodon.net/tag/00ZQ)
- 3.4.2.11 の一般定理は `[ModelCategory C]`、局所可呈示性、cofibrantly generated と弱同値の押し出し安定性を仮定する。具体的な `C = SSet` で instance なし。単体集合で適用できる別宣言は通常の押し出しの場合に限られるため partial とした。 [3.4.2.11](https://kerodon.net/tag/011A)

項目ごとの本文のタグ、Lean の型・公理、検査時のコミットは `ch3-kernel-evidence.json`。型クラス合成の結果は `ch3-model-instance.json`。
