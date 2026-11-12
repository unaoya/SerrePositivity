module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ChosenColimitPointwise
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.FunctorPointwiseColimitCriterion
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PointwiseColimitPrecomposition
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentCoconeTransport
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.InitialTransport

/-!
概要：指定形状の余極限が標的に全て存在すれば関手圏の余極限は各点で計算される。
方針：選んだ点ごとの普遍余錐族と、元の指定余錐の一意比較を使う。
規約：元の指定余錐の評価を結論に保つ。
使われ方：有限余積の全比較の関手が生成操作を保存することの検証。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories


/-- 概要：指定形状の余極限存在から点ごとの普遍余錐を選べる。
方針：選んだ余錐族の変数交換を元の底図式へ輸送する。
規約：元の全図式を保持する。
使われ方：元の指定余錐との一意比較。 -/
lemma exists_pointwiseColimitCocone {J A X : SSet.{u}} [Quasicategory X]
    (hX : ∀ p : J ⟶ X, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit p) (p : J ⟶ (ihom A).obj X) :
    ∃ d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p, _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.IsPointwiseColimitCone d := by
  let U := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv J A X p
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv A J X U = p :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv J A X).left_inv p
  exact ⟨_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentCoconeOfDiagramEq he (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.chosenColimitParameterCocone hX U),
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pointwiseColimitCocone_diagramEq he _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.chosenColimitParameterCocone_isPointwiseColimit hX U)⟩

/-- 概要：同じ全図式上で同型な余錐は点ごとの余極限性も共有する。
方針：同じ coslice の同型を全ての評価へ写す。
規約：元の全余錐の同型を使う。
使われ方：選んだ点ごとの余錐から元の余錐へ戻す。 -/
lemma pointwiseColimitCone_of_vertexIso {J A X : SSet.{u}} [Quasicategory X]
    {p : J ⟶ (ihom A).obj X} {c d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p}
    (hc : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.IsPointwiseColimitCone c) (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p) c d) :
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.IsPointwiseColimitCone d := by
  intro a
  exact (hc a).of_vertexIso
    ((hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a))).toFunctor.mapIso e)

/-- 概要：元の関手圏の指定余極限余錐は各点でも普遍。
方針：点ごとの普遍余錐と同じ coslice の一意な同型を使う。
規約：元の標的に指定形状の余極限存在だけを要求する。
使われ方：後合成関手の余極限保存。 -/
lemma isPointwiseColimitCone_of_hasColimits {J A X : SSet.{u}} [Quasicategory X]
    (hX : ∀ p : J ⟶ X, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit p) {p : J ⟶ (ihom A).obj X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.IsPointwiseColimitCone c := by
  obtain ⟨d, hd⟩ := exists_pointwiseColimitCocone hX p
  exact pointwiseColimitCone_of_vertexIso hd
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitConeIso d c (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.isColimitCone_of_pointwise d hd) hc)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
