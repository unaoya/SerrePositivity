# M5：dg 理論の独立入口

U0〜U6 実装・検証（U7〜U10継続中）：2026-10-15。計画は
[ dg-theory.md ](../../formalization-plans/dg-theory.md)。
入口は [StageThree.lean](StageThree.lean)（U0〜U6）、[StageTwo.lean](StageTwo.lean)（U0〜U5）、[StageOne.lean](StageOne.lean)（U0〜U3）。共有ルート import は変更しない。

Lean `v4.35.0-rc4`、Mathlib `e6bbacd0e1b7307ff6e17da09cd2455f60804fa6`。
Mathlib HEAD と lake-manifest を再照合済み。依存更新なし。
追加宣言の namespace は `SerrePositivity.DifferentialGraded`。

## 宇宙・次数・順序

`A : Type u`、`[CommRing A]`、`Complex A = CochainComplex (ModuleCat.{u} A) ℤ`。
環と Hom 加群の宇宙は初期 API では同じ `u`、dg 圏の対象 `D : Type v` は独立。
`Complex A : Type (u + 1)`、各斉次 Hom と Z⁰/H⁰ の Hom は `Type u`。
加群対象の宇宙は `Type (max (u+1) v)`。Hom end とその豊穣圏には `[Small.{u} D]` を明示する。
より大きい Hom 宇宙・局所化・解像度の存在は後続で個別に指定する。

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

| [Complexes/Braiding.lean](Complexes/Braiding.lean) | signed braiding の自然性・両hexagon、`SymmetricCategory` |
| [Complexes/Currying.lean](Complexes/Currying.lean)、[Closed.lean](Complexes/Closed.lean)、[Enrichment.lean](Complexes/Enrichment.lean) | 全次数 tensor–Hom 随伴・三変数自然性・閉構造・自己豊穣との一致 |
| [Module/Basic.lean](Module/Basic.lean)、[Representable.lean](Module/Representable.lean) | 豊穣右加群、opposite の符号、右代表加群 |
| [Module/Hom.lean](Module/Hom.lean)、[Action.lean](Module/Action.lean) | 全次数自然性の Hom end、`GradedNatTrans` とのパラメータ同値、作用の成分公式 |
| [Module/Composition.lean](Module/Composition.lean)、[Category.lean](Module/Category.lean) | Hom end の単位・合成、Mathlib 豊穣加群圏、閉零圏・評価関手 |
| [Module/Yoneda.lean](Module/Yoneda.lean) | 全パラメータ dg Yoneda と Hom 複体の chain iso |
| [Module/Ring.lean](Module/Ring.lean) | 一対象 A の対象復元、Hom 複体比較、通常非有界複体圏との同値 |
| [Module/Tensor.lean](Module/Tensor.lean)、[Free.lean](Module/Free.lean)、[Underlying.lean](Module/Underlying.lean) | 自由加群の全次数作用・関手、離散対象族への忠実な忘却 |
| [Module/ClosedMaps.lean](Module/ClosedMaps.lean)、[TensorAdjunction.lean](Module/TensorAdjunction.lean) | 全次数自然な chain map 族との同値、free/evaluation 随伴・自然性 |
| [Module/FreeHom.lean](Module/FreeHom.lean)、[FreeHomNaturality.lean](Module/FreeHomNaturality.lean) | 全次数 Hom 複体の chain iso・K/M自然性・通常随伴との閉零比較 |

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
lake build SerrePositivity.DifferentialGraded.Checks.Modules
lake env lean SerrePositivity/DifferentialGraded/Checks/Modules.lean
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
U5 は dg opposite、右代表加群、全次数 Hom end による主豊穣加群圏、
`moduleHom (representable x) M ≅ M(x)`、一対象 A の普通複体との比較まで完成した。
Mathlib の現行 `EnrichedNatTrans.out` は閉零の通常自然性なので、全次数の代用には使わない。
[ModulesAcceptance.lean](Checks/ModulesAcceptance.lean) は正負次数・任意 A・ℤ・ZMod 2 を検証する。
U4/U5の追加監査38宣言、合計79宣言は標準公理のみ。
U6の free/forget、自由評価随伴、全次数 Hom 同型と自然性は完成した。
U6の追加監査35宣言、U0〜U6合計114宣言。検証と引継ぎは計画§13。
次は shift/cone・極限余極限、objectwise quasiIso・局所化・semifree。
U7a1では `Module/Zero.lean` に全次数零加群・零対象・評価による零対象性の判定を追加した。
`Complexes/Zero.lean` の零 Hom 複体とともに `Checks/Zero.lean` で検証する。
U7a2の `Module/Biproduct.lean` は objectwise 二項直和の全次数対角作用、
射影・包含、積と余積の普遍性、有限直和の存在と評価比較を供給する。
受入入口は `Checks/Biproduct.lean`。shift/cone・残る極限余極限は引き続き未完。
U7b1では `Complexes/Shift.lean` に次数 p の符号 `(-1)^(sp)` を持つ shift dg 関手、
`Module/Shift.lean` に整数ごとの加群 shift 関手と評価自然同型を構成した。
受入入口は `Checks/Shift.lean`。
U7b2の `Module/ShiftCoherence.lean` は零・加法比較の全次数自然性・結合/零の整合性から
`HasShift ℤ` を登録し、加法性と評価の `CommShift ℤ` を証明する。
受入入口は `Checks/ShiftCoherence.lean`。cone と必要な残る極限余極限は未完。
API契約と共有 G1/G2/G5/G6 への引継ぎは計画§12.8。
導来圏・射影モデル・dg 商・Morita・Perf と M5全体は未完成。
一般モデル圏・Quillen・転送・SM7 は共有系列が所有し、この入口には置かない。
引用候補の採用状況は [Inputs の台帳](../Inputs/DifferentialGraded/README.md)。
