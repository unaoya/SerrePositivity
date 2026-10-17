# U13 全体の受入照合と残項目

正本は `dg-theory.md` §15.3 と §17.86–17.113。
任意可換環、非有界cochain複体、dの次数+1、ホモトピー次数−1、Mathlib Enrichedを維持する。
**U13全体の最終受入は進行中。** 一対象環の既存PerfectHomotopyでの有限射影代表は未完である。
既存のKaroubi包絡を付けた比較だけで、元の比較の本質的全射を結論しない。

## 要件の棚卸し（2026-10-17）

| 項目 | 現在の証拠・判定 |
| --- | --- |
| U13a：指定生成元のfinite cell、有限support、全Hom射影性 | 既存証明あり。`FiniteCell`, `FiniteCellProjective`。§17.74–75で受入済み |
| U13b：主導来圏内のfinite cellのretractとしてのPerf、thick閉性、Karoubi比較 | 既存証明あり。`Basic`, `Triangulated`, `KaroubiEquivalence`, `UniversalProperty`。§17.76–80・87 |
| U13c：代表加群のcompact性、Perf⇒compact、小さいcompact生成族 | 既存証明あり。`RepresentableHomology*`, `RepresentableCoproduct*`, `PerfectCompact`, `Generators`。§17.81–86 |
| U13d：compact⇒Perf | 現在は引用なしの証明あり。`CompactConverse.moduleCompact_iff_perfect`。§17.113以前の未完記録は現状の判定に使わない。U14c.11でも実際に適用・公理監査済み |
| U13e：全Homを持つ射影的perfect dg enhancement、H⁰の線形同値 | 既存証明あり。`Enhancement`, `EnhancementLinear`。§17.88 |
| U13e：finite cellの小さい代表系、Perfの本質的小性、小さいdg enhancement | 既存証明あり。`SmallStages`, `SmallStageCover`, `EssentiallySmall`, `SmallEnhancement`。§17.89–90 |
| U13e：実際の整数shift、零・加法coherence、標準dg cone三角形との一致 | 既存証明あり。`EnhancementShift*`, `EnhancementTriangulated`, `EnhancementConeComparison`。§17.91–98 |
| U13e：小さい代表系へのshift・三角構造と包含の整合性 | 既存証明あり。`SmallEnhancementTriangulated`。§17.94 |
| U13e：一対象Aと非有界複体・既存PerfectHomotopyの全Hom・線形・shift・三角比較 | 既存証明あり。`StrictComplex*`, `RingPerfectComparison`, `RingPerfectTriangulated`。§17.99–110 |
| U13e：finite cellの有限射影評価、主Perfの比較像へのretract表示 | 既存証明あり。`RingFiniteCell`, `RingRetract`。§17.108・111 |
| U13e：Karoubi実現・元の比較へのfactorと導来・三角図式の整合性 | 既存証明あり。`RingKaroubi`, `RingKaroubiFactors`。§17.112–113 |
| U13e：実際の射影的perfect dg enhancement内でのホモトピー冪等分裂 | 今回証明。以下U13e.27。分裂対象は実際の射影的perfect dg加群である |
| U13e：既存PerfectHomotopy自身のホモトピー冪等分裂 | 未完・必須。分裂対象に有界有限射影複体の代表が必要。前行の一般dg加群での分裂だけでは足りない |
| U13e：主Perfのretractの有界有限射影代表、Karoubiなしの本質的全射 | 未完・必須。`perfectHomotopyToDGPerfect` と実際のdg比較の本質的全射を証明する必要がある |

## U13e.27：実際のenhancementのホモトピー冪等分裂

- `Perfect/EnhancementIdempotents.lean`：主Perfの既存冪等完備性を既存U13同値で運び、
  全射影的perfect H⁰と小さい代表系のH⁰の冪等完備性を証明した。
- `perfectDGModule_homotopyIdempotent_splits` は、閉零射pに対する
  `boundaryRelation (p ≫ p) p` から実際の射影的perfect dg加群Yと閉零射i,rを構成する。
  i≫rと恒等射、r≫iとpの一致を同じ全Hom複体の境界関係で証明した。
  strict chain idempotentであることを仮定していない。
- `Perfect.ChecksEnhancementIdempotents` 対象ビルド成功（2490 jobs）。
  主要4宣言の公理は `propext`, `Classical.choice`, `Quot.sound` のみ。
  既存のPerfectファイル・PerfectComplex・Idempotent一般論を編集していない。

## 既存項目の再検証

- finite cell・全Hom射影性・PerfとKaroubi・compact生成・compact⇒Perf・
  小さいenhancement・標準cone比較・既存PerfectHomotopy比較・retract表示・Karoubi factorの
  17既存監査対象を合同ビルドし、3240 jobsで成功した。
- 274件の公理監査出力はすべて標準3公理のみ。
  この再検証は既存項目の証拠であり、未完の有限射影代表・元の比較の本質的全射を証明したことにはしない。

## 範囲の区別

- 元の各chain代表そのものへのstrict idempotentの持ち上げは受入条件にしない。
  必要なのは、ホモトピー圏で分裂し、分裂対象が有界有限射影複体で表されること。
  同じ複体上のstrict冪等元であることとホモトピー冪等性を同一視しない。
- 任意dg圏の各評価成分が有界有限射影であることは要求しない。一般dg圏のU13eは
  実際の射影的perfect dg加群の全Hom enhancementを使い、有界有限射影代表の照合は一対象環Aの場合である。
- 任意の可換環のPerfectHomotopyに通常のtruncationが閉じるとは仮定しない。
  有界t構造の冪等完備性を適用するためのt構造を、証明なしに置かない。
- D4mのモデル比較、U14–17のMorita・商の作業はU13全体の今回の受入範囲外。
  他担当のQuotient・Verdier・Bimodule・Tensor・Resolution・指定Derived系列は編集しない。
- DG-PER等の引用は採用していない。必要となれば、採用せず停止・報告する。

## 残る作業

1. 一対象Aのホモトピー冪等元の分裂対象に有界有限射影代表を与える。
2. その証拠で既存PerfectHomotopyの冪等完備性と、元の比較の本質的全射・同値を証明する。
3. retract・線形・shift・三角図式を既存比較に接続して最終照合する。
4. 項目ごとの対象ビルド・主要宣言の公理監査を揃え、この記録を最終受入へ更新し、
   `dg-theory.md`へ参照を一行だけ追加する。
