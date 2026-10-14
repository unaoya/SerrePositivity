# M5：dg 理論の独立入口

U0〜U4 実装・検証（U5進行中）：2026-10-15。計画は
[ dg-theory.md ](../../formalization-plans/dg-theory.md)。
入口は [StageOne.lean](StageOne.lean)。共有ルート import は変更しない。

Lean `v4.35.0-rc4`、Mathlib `e6bbacd0e1b7307ff6e17da09cd2455f60804fa6`。
Mathlib HEAD と lake-manifest を再照合済み。依存更新なし。
追加宣言の namespace は `SerrePositivity.DifferentialGraded`。

## 宇宙・次数・順序

`A : Type u`、`[CommRing A]`、`Complex A = CochainComplex (ModuleCat.{u} A) ℤ`。
環と Hom 加群の宇宙は初期 API では同じ `u`、dg 圏の対象 `D : Type v` は独立。
`Complex A : Type (u + 1)`、各斉次 Hom と Z⁰/H⁰ の Hom は `Type u`。
より大きい Hom 宇宙、加群圏・局所化の宇宙は後続で個別に指定する。
この入口から smallness・局所小性・解像度の存在は推論しない。

複体は非有界。noetherian・体・標数・有限次元・有限生成の仮定なし。
微分はコチェイン次数 +1、contracting homotopy は −1。
原論文のホモロジー次数 i はコチェイン次数 −i に対応する。

Mathlib の豊穣合成は Hom(x,y)⊗Hom(y,z) → Hom(x,z)。
通常順 μ(g,f)=g∘f は g⊗f の順で、`dμ(g,f)=μ(dg,f)+(-1)^q μ(g,df)`。
`forward_eq_signed_compose` は `forward(f,g)=(-1)^(pq) compose(g,f)` を証明する。
Ch(A) の `enrichedComposition` は既存 signed symmetry の後に通常順 `composition` を合成する。
`enrichedComposition_component` と `enrichedComposition_apply` がこの式を直接検証する。

## API と再利用

| ファイル | 提供するもの |
| --- | --- |
| [Complexes/HomComplex.lean](Complexes/HomComplex.lean) | `linearHomComplex` 再利用、Leibniz、閉零次数と chain map、contracting homotopy |
| [Complexes/Composition.lean](Complexes/Composition.lean) | 非有界 tensor の `tensorLift`、通常順合成の chain map、Koszul 比較 |
| [Complexes/CompositionLaws.lean](Complexes/CompositionLaws.lean) | 豊穣順の単位・結合、成分 constructor/accessor の往復 |
| [Complexes/Monoidal.lean](Complexes/Monoidal.lean) | Ch(A) 固有の tensor の加法性・A 線形性と成分公式 |
| [Complexes/Unit.lean](Complexes/Unit.lean)、[UnitBoundary.lean](Complexes/UnitBoundary.lean)、[UnitTensor.lean](Complexes/UnitTensor.lean) | 単位からの射と零次数 cycle、元の複体の −1 境界との一致、tensor 評価 |
| [Category/Basic.lean](Category/Basic.lean) | Mathlib `EnrichedCategory` の別名、`ofComponents`、Z⁰ と A 線形性 |
| [Category/Components.lean](Category/Components.lean) | 斉次 Hom、通常順合成、Leibniz・単位・結合 |
| [Category/Examples.lean](Category/Examples.lean) | Ch(A) と一対象 A の豊穣、既存 chain map 圏との同値、`EnrichedOrdinaryCategory` |
| [Category/Homotopy.lean](Category/Homotopy.lean) | Mathlib `Quotient` による H⁰、境界判定、A 線形商関手 |
| [Category/Comparison.lean](Category/Comparison.lean) | Ch(A) の H⁰ 等式と既存 chain homotopy の一致 |
| [Functor/Basic.lean](Functor/Basic.lean)、[QuasiEquivalence.lean](Functor/QuasiEquivalence.lean) | Mathlib `EnrichedFunctor`、A 線形 H⁰ 関手、準同値と identity/comp |

`PerfectComplex/Tensor.lean` と `TensorSymmetry.lean` を import して再利用する。
既存ファイルは編集しない。通常の PerfectHomotopy は後続 D6 の比較先として維持する。
Z⁰ は `ForgetEnrichment` の単位からの射の圏であり、`closedHomEquiv` が閉零次数の元と同一視する。
H⁰ はその射の差が `d : Hom⁻¹ → Hom⁰` の像に入る関係の商。
`toHomotopy_map_eq_iff_boundary` が「生成された余分な関係ではない」ことを保証する。
一般の H⁰ を三角圏とはしない。

## 検証と残る境界

```sh
lake build SerrePositivity.DifferentialGraded.Checks.Axioms
lake env lean SerrePositivity/DifferentialGraded/Checks/Axioms.lean
```

[Acceptance.lean](Checks/Acceptance.lean) は任意 A、次数 0/−1/1、ZMod 2、H⁰ の A 線形性を検証する。
空圏 → 一対象 A は Hom 準同型だが本質的全射でなく、
非零 A → 零 dg 圏は本質的全射だが Hom 準同型でない。二条件は別々に必要。
[Axioms.lean](Checks/Axioms.lean) の主要 41 宣言はすべて
`propext`・`Classical.choice`・`Quot.sound` のみ。新規 sorry・引用 axiom なし。
ローカル import の推移的閉包に Spectra・Paper・Inputs は含まれない。

U4 の全整数次数 tensor–Hom 随伴、三変数自然性、signed braiding の自然性・両hexagon、
SymmetricCategory/MonoidalClosed 登録は完成した。
`Complexes/Enrichment.lean` の `complexEnrichment_eq_closed` は、閉構造由来の
Mathlib 自己豊穣とU1の単位・合成の一致を証明する。
`Checks/Braiding.lean`、`Checks/Closed.lean`、`Checks/Enrichment.lean` で検証・公理監査済み。
U5 はその braiding を使う dg opposite、右代表加群・Yoneda・Hom end。
dg 加群・導来圏・射影モデル・dg 商・Morita・Perf はまだ構成していない。
一般モデル圏・Quillen・転送・SM7 は共有系列が所有し、この入口には置かない。
引用候補の採用状況は [Inputs の台帳](../Inputs/DifferentialGraded/README.md)。
