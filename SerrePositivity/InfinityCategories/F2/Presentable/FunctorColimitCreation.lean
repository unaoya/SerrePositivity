module

public import SerrePositivity.InfinityCategories.F2.Presentable.ChosenColimitPointwise
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorPointwiseColimitCriterion
public import SerrePositivity.InfinityCategories.F2.Presentable.PointwiseColimitPrecomposition
public import SerrePositivity.InfinityCategories.HomotopyLimits.CoherentCoconeTransport
public import SerrePositivity.InfinityCategories.Core.InitialTransport

/-!
概要：指定形状の余極限が標的に全て存在すれば関手圏の余極限は各点で計算される。
方針：選んだ点ごとの普遍余錐族と、元の指定余錐の一意比較を使う。
規約：元の指定余錐の評価を結論に保つ。
使われ方：有限余積の全比較の関手が生成操作を保存することの検証。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits

/-- 概要：指定形状の余極限存在から点ごとの普遍余錐を選べる。
方針：選んだ余錐族の変数交換を元の底図式へ輸送する。
規約：元の全図式を保持する。
使われ方：元の指定余錐との一意比較。 -/
lemma exists_pointwiseColimitCocone {J A X : SSet.{u}} [Quasicategory X]
    (hX : ∀ p : J ⟶ X, HasColimit p) (p : J ⟶ (ihom A).obj X) :
    ∃ d : JoinCocone p, IsPointwiseColimitCone d := by
  let U := internalHomFlipHomEquiv J A X p
  have he : internalHomFlipHomEquiv A J X U = p :=
    (internalHomFlipHomEquiv J A X).left_inv p
  exact ⟨coherentCoconeOfDiagramEq he (chosenColimitParameterCocone hX U),
    pointwiseColimitCocone_diagramEq he _
      (chosenColimitParameterCocone_isPointwiseColimit hX U)⟩

/-- 概要：同じ全図式上で同型な余錐は点ごとの余極限性も共有する。
方針：同じ coslice の同型を全ての評価へ写す。
規約：元の全余錐の同型を使う。
使われ方：選んだ点ごとの余錐から元の余錐へ戻す。 -/
lemma pointwiseColimitCone_of_vertexIso {J A X : SSet.{u}} [Quasicategory X]
    {p : J ⟶ (ihom A).obj X} {c d : JoinCocone p}
    (hc : IsPointwiseColimitCone c) (e : VertexIso (X := sliceUnder p) c d) :
    IsPointwiseColimitCone d := by
  intro a
  exact (hc a).of_vertexIso
    ((hoFunctor.map (sliceUnderPostcomp p (evaluateFunctorAt a))).toFunctor.mapIso e)

/-- 概要：元の関手圏の指定余極限余錐は各点でも普遍。
方針：点ごとの普遍余錐と同じ coslice の一意な同型を使う。
規約：元の標的に指定形状の余極限存在だけを要求する。
使われ方：後合成関手の余極限保存。 -/
lemma isPointwiseColimitCone_of_hasColimits {J A X : SSet.{u}} [Quasicategory X]
    (hX : ∀ p : J ⟶ X, HasColimit p) {p : J ⟶ (ihom A).obj X}
    (c : JoinCocone p) (hc : IsColimitCone c) : IsPointwiseColimitCone c := by
  obtain ⟨d, hd⟩ := exists_pointwiseColimitCocone hX p
  exact pointwiseColimitCone_of_vertexIso hd
    (colimitConeIso d c (isColimitCone_of_pointwise d hd) hc)

end SerrePositivity.InfinityCategories.F2.Presentable
