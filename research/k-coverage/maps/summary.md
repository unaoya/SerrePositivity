# 停止点 3　K 理論の文献地図

照合基点は `6e6a3f9a7`。旧表 208 行のうち旧候補が宣言名で指定された 105 行について、延べ 212 件、異なる 174 宣言を型と公理で確認した。候補名のない行では対応表と文献別の検索記録を使った。型検査は Lean 4.35.0-rc4 の共有ロック下で既存の olean を使用。追加検査は 134 宣言で、残る 186 宣言はソースと推移的 import が同一の段 1・2 の出力を用いた。

[補助 12 文献の 47 行](others.csv) · [補助文献の検索記録](others-none-search.json) · [旧表の 208 行](legacy-kernel.csv) · [型と公理](legacy-kernel-evidence.json)

## 文献ごとの件数

主要 5 文献は 641 項目。KST・Land–Tamme の集計には、段 1 の partial 91 件の再判定を反映した。補助 12 文献は旧表の 47 項目。none に主要 5 文献の見出し・記法も含む。[段 1 再判定](stage1-partial-review.csv)

| 文献 | own | mathlib | both | partial | interface | none | 計 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| [論文 §3–4](paper/items.csv) | 8 | 0 | 0 | 7 | 7 | 40 | 62 |
| [KST](kst/items.csv) | 4 | 0 | 0 | 7 | 12 | 127 | 150 |
| [Land–Tamme](land-tamme/items.csv) | 0 | 0 | 0 | 10 | 6 | 116 | 132 |
| [Tamme](tamme/items.csv) | 9 | 0 | 0 | 10 | 0 | 31 | 50 |
| [BGT](bgt/items.csv) | 4 | 0 | 0 | 10 | 0 | 233 | 247 |
| Waldhausen | 0 | 0 | 0 | 1 | 0 | 8 | 9 |
| Barwick | 0 | 0 | 0 | 0 | 0 | 2 | 2 |
| Thomason–Trobaugh | 0 | 0 | 0 | 0 | 0 | 9 | 9 |
| Thomason | 0 | 0 | 0 | 1 | 0 | 1 | 2 |
| Neeman | 0 | 1 | 0 | 0 | 0 | 3 | 4 |
| 9 人論文 | 0 | 0 | 0 | 5 | 0 | 1 | 6 |
| Drinfeld | 3 | 0 | 0 | 3 | 0 | 2 | 8 |
| Kuznetsov–Lunts | 1 | 0 | 0 | 1 | 0 | 0 | 2 |
| Schlichting | 0 | 0 | 0 | 0 | 0 | 2 | 2 |
| Balmer–Schlichting | 1 | 0 | 0 | 0 | 0 | 0 | 1 |
| Goodwillie | 0 | 0 | 0 | 0 | 0 | 1 | 1 |
| Stacks | 0 | 0 | 0 | 1 | 0 | 0 | 1 |
| 計 | 30 | 1 | 0 | 56 | 25 | 576 | 688 |

## 旧表の status と検査後の判定

複合行は対応する項目の判定を全件記録した。集計上は全項目が一致する場合に完全対応、一つでも直接の対応があり他に差がある場合に partial とした。界面だけが対応する場合は interface。凍結は独立した欄で、実在する候補の所属に基づく。

| 旧 status | own | mathlib | both | partial | interface | none | 計 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| proved | 12 | 0 | 0 | 22 | 2 | 8 | 44 |
| partial | 0 | 0 | 0 | 8 | 1 | 31 | 40 |
| interface | 0 | 0 | 0 | 1 | 2 | 7 | 10 |
| sorry | 0 | 0 | 0 | 0 | 3 | 1 | 4 |
| frozen | 1 | 0 | 0 | 4 | 0 | 10 | 15 |
| none | 0 | 1 | 0 | 3 | 8 | 83 | 95 |
| 計 | 13 | 1 | 0 | 38 | 16 | 140 | 208 |

`sorryAx` を検出した 6 宣言は型と公理の記録にある。旧表の「proved」は、公理の確認と原典との対応をともに要する。有限 Zariski Čech 条件と二つの降下補題は `ModelCategory SSet` を要求する。段 1 の型クラス検査ではこの instance の合成に失敗した。[型クラス検査](kst/model-category-evidence.json)

## README の「K の計画の問題」10 点

1. **KST §4 への依存。** KST 5.2 では 4.12 が、5.5 では 4.13 と 4.8 が使われる。4.8 の近接宣言は非正 dg 代数の塔に対し `IsKConnective` を仮定して不変量のプロ同値を移す。K 自身の証人も、4.13 の Noether 単体環から π₀ への K のプロ比較も確認できない。Land–Tamme 2.35 は 4.11 の比較に対応するが、4.8 と 4.13 をこの経路で供給するには別の比較が残る。[KST §4–5](kst/items.csv) · [Land–Tamme 2.31–2.36](land-tamme/items.csv)

2. **K の 1-connectivity。** Land–Tamme 2.31 の dg 版は、`IsKConnective` を仮定して実 Perf 値の連結度と弱同値を移す。2.4・2.6(i) のように K にその証人を与える型は確認できなかった。凍結した L2 の単位的単体環に対する GL・plus の部分と、2.4 の K の連結度の間にも比較が要る。[Land–Tamme 2.4・2.6(i)・2.31](land-tamme/items.csv) · [L2 の凍結](../../../formalization-plans/archive/stage-i/kst-lanes/L2-comparison.md#L3)

3. **公理 (3) の冪零不変性。** `Nilinvariant` は次数付き前層に課す条件で、`piDescent_iff_reduction` はその条件を使う。本論文の係数付き L がこの条件を満たす証明も、Land–Tamme 3.5 の切断性からの導出も確認できない。計画の D9 が指定する離散結合環の有理 K 比較には GL・plus と有理ホモロジーの比較が残る。[本論文 §3.1・§3.3](paper/items.csv) · [Land–Tamme 3.5](land-tamme/items.csv) · [計画 D9](../../../formalization-plans/archive/stage-i/kst-lanes/k-theory-kst-route.md#L247)

4. **KST §5 の K と pro の担当。** 5.1 の有限 Zariski Čech 条件は前層の界面で、SSet のモデル圏も既存の検査環境で合成できなかった。5.2–5.6 では有限型の幾何、通常のブローアップの冪同型、Koszul の塔の候補がある。K を適用した正方形とその合成は残る。決定 13 が K-L6 に割り当てた部分は決定 16 の凍結後に再割当が必要という README の記述と整合する。[KST §5](kst/items.csv) · [型クラス検査](kst/model-category-evidence.json) · [決定 13・16](../../../formalization-plans/archive/stage-i/kst-lanes/k-theory-kst-route.md#L467)

5. **凍結中の pro の部品。** `Tower` と次数別 `IsProEquivalence`・`IsProCartesian`、Koszul の 4.9・4.10 を確認した。4.9 は有限生成加群の正次数の Koszul ホモロジーのプロ消滅。4.10 は各次数の加群複体でのプロ同型で、原典の単体環の導来商との比較は残る。4.6 のホモトピー引き戻しとファイバー比較の同値、正方形の合成には `IsProCartesian` の定義以上の結論が要る。[KST §4](kst/items.csv) · [新基準での再判定](stage1-partial-review.csv) · [L6 の凍結](../../../formalization-plans/archive/stage-i/kst-lanes/L6-pro-excision.md#L3)

6. **Land–Tamme 2.35。** 原典の後段は Corollary 2.35 を KST 4.11 に対応づける。2.32 は連結プロ環の四角形全体を扱う。Lean には単一 dg Milnor 正方形の実 resolved 商での引き戻しと、`IsKConnective` と正次数 Tor の模型を仮定した塔の一本の比較がある。原典の導来商のプロ四角形を組み、係数付きの場合に K を適用する型は確認できない。[Land–Tamme 2.32–2.36](land-tamme/items.csv) · [旧表 115–119 行の検査](legacy-kernel.csv)

7. **非連結 K の登録。** BGT 8.1 に対応する Sp 値の保存条件と、固定 dg 入力の懸垂塔の実余極限は確認した。BGT §9.3 の帰結として必要な、小安定圏の非連結 K が任意の完全列をファイバー列に送る登録は確認できない。Tamme 15・18 の対応は小安定圏の右脚自体に充満忠実な右随伴がある場合で、Ind に課す原典の切除性だけからの小圏の完全列は残る。9 人論文 A.3.12 に対応する Karoubi 列と Ind 上の Verdier 列の比較も確認できない。[BGT 8.1・9.6・§9.3](bgt/items.csv) · [Tamme 15・18](tamme/items.csv) · [補助文献](others.csv)

8. **計画文書と引用番号。** 旧経路の冒頭・§2.3・D6 は ⊙ または 2.32 を使わないとし、決定 16 は Land–Tamme の ⊙ へ移すとする。BGT v4 9.8 は共表現で、§9.3 が局所化をその帰結として述べる。KST 2.10 はこの帰結を引用しており、版の取り違えはない。Land–Tamme 3.12 は旧表 122 行、B.2 は 128 行で `not_required`、両者をまとめた 131 行では `unknown`。経路 §2.4・D4 は、前者を Drinfeld 1.6.3 で置き換え、後者の Perf を降下データで定義する。地図では両方を `unknown` とした。[旧表 122 行](../items.csv#L122) · [128 行](../items.csv#L128) · [131 行](../items.csv#L131) · [計画 §2.3–2.4](../../../formalization-plans/archive/stage-i/kst-lanes/k-theory-kst-route.md#L113) · [D4・D6](../../../formalization-plans/archive/stage-i/kst-lanes/k-theory-kst-route.md#L242) · [決定 16](../../../formalization-plans/archive/stage-i/kst-lanes/k-theory-kst-route.md#L470)

   番号の誤記は二つある。KST `§10-7` は計画書内の参照で、原典に該当する節はない。Land–Tamme `§1.2` は原典に存在しない小節で、⊙ は Theorem 1.3 の証明に現れる。Definition 1.2 は完全列と局所化不変量を定義する。[§10-7 の計画書内参照](../../../formalization-plans/archive/stage-i/kst-lanes/L4-derived-geometry.md#L24) · [Land–Tamme の計画書内参照](../../../formalization-plans/archive/stage-i/kst-lanes/L1b-ks2.md#L45) · [Lean の引用箇所](../../../SerrePositivity/KST/SConstruction/DGLaxQuotientEnd.lean#L11)

9. **本論文と Lean の型。** 3.1 の `theorem_3_1_K0` は離散 Noether 局所基底とパラメータ台で、不変類の正整数倍を持ち上げる型を持ち、`sorryAx` に依存する。`supportedRankK0_descent` も台つきランク商の三角 K₀ の不変類の正整数倍を持ち上げる降下入力として `sorryAx` に依存し、`theorem_4_7_K0` と `theorem_4_7` に伝播する。3.5 の共役和にも 3.1 側の依存がある。局所環上の有限自由版と支持付き有限射影版の三角 K₀ の比較は `freePerfectK0Equiv` が供給する。`triangulatedKZeroNatIso` は安定圏模型の連結 BF K の π₀ と三角 K₀ を比較する。これを本論文の支持付き係数 K の π₀ に結ぶ型と、4.6 の中央 A 線型な連結係数代数の表示は確認できない。4.2 の Karoubi 包と 4.5 の正規化長側の階数倍は確認済みで、F5 の迂回には係数版の K₀・K₋₁ の局所化列と、その降下の比較が要る。[本論文 §3–4](paper/items.csv) · [kernel の型・公理](legacy-kernel-evidence.json) · [有限自由版の比較](../../../SerrePositivity/PerfectComplex/Perfect/FreeComparison.lean#L170) · [連結 BF K の π₀](../../../SerrePositivity/KST/SConstruction/TriangulatedKZeroNatIso.lean#L51) · [M9/F5](../../../formalization-plans/archive/stage-i/kst-lanes/k-theory-kst-route.md#L324)

10. **本論文の最初の二段と計画 v2。** 原典は Goodwillie の有理比較で無限小 K を切断型とし、Land–Tamme A.2・B.3 の係数付き cdh 降下を使う。どちらの適用も Lean では確認できない。計画 v2 の置換に必要な KST A・3.7 の大域的なプロ降下・完全圏の半直交分解も確認できず、現状ではチャート比較と降下の入力がある。Drinfeld の dg 商と解消は確認したが、1.6.3 の任意の h-flat dg 圏とのテンソルでの商比較は確認できない。[本論文 §3.1](paper/items.csv) · [KST A・3.7](kst/items.csv) · [Land–Tamme A.2・B.3](land-tamme/items.csv) · [Goodwillie・Drinfeld](others.csv)

## 補助文献の番号と帰属

- Thomason–Trobaugh 3.19 は閉台の近傍に沿う切除。5.1 と 7.4 はそれぞれ連結 K と Bass 非連結 K の局所化。5.2.2–5.2.4 は完全複体の延長、射、零射を扱う。[1990 刊行版](https://gwern.net/doc/math/1990-thomason.pdf)
- 旧表の Neeman Cor 3.2.3 は Bondal–van den Bergh の番号で、稠密部分圏での `X ⊕ X[1]` の主張。qcqs スキームでの compact＝perfect は同論文の Thm 3.1.1。Neeman 9.1.5 の帰属は KST 3.13 の [Nee01]、主張は著者自身の 2011 年論文の再掲で確認した。右直交の対象への Hom の比較は Mathlib にある。[Bondal–van den Bergh v2](https://arxiv.org/abs/math/0204218v2) · [Neeman 2011, Reminder 5.1](https://www.numdam.org/item/10.24033/asens.2151.pdf)
- Waldhausen 1.8.1 は懸垂系で弱同値まで cofibration が分裂する場合の比較。Barwick v6 7.4 は理論の加法性の特徴づけで、generic fibration は 8.9・9.24。Schlichting の刊行版 §7 Lemma 6 の帰属は BGT の引用で確認した。主張は公開稿 6.4 で照合した。[Waldhausen 1985](https://noah.nrw/ubbihs/content/titleinfo/5112640) · [Barwick v6](https://arxiv.org/abs/1204.3607v6) · [Schlichting 公開稿](https://webhomes.maths.ed.ac.uk/~v1ranick/papers/schlneg.pdf)
