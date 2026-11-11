module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoconeValEquality
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorCoconeEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PreFiberKan
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CoherentCoconeTransport

/-!
概要：元の点ごとの余極限余錐を、関手の定義域の前合成と図式の等号で輸送する。
方針：同じ全余錐の評価を元の評価へ厳密に戻す。
規約：余錐の頂点や脚を選び直さない。使われ方：WithInitial の模型から元の錐形状へ戻す。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 元の点ごとの余極限は、関手の定義域の任意の前合成で保たれる。 -/
lemma pointwiseColimitCocone_precomp {J K A X : SSet.{u}} [Quasicategory X]
    {p : J ⟶ (ihom K).obj X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (hc : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.IsPointwiseColimitCone c)
    (a : A ⟶ K) : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.IsPointwiseColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone ((pre a).app X) c) := by
  intro k
  have hv : (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.evaluateFunctorCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone ((pre a).app X) c) k).val =
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.evaluateFunctorCocone c (a.app _ k)).val := by
    change (c.val ≫ (pre a).app X) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k = c.val ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt _
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.evaluateFunctorAt_pre]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isColimitCone_iff_of_cocone_val_eq _ _ hv).mpr (hc (a.app _ k))

/-- 元の図式の等号による全余錐の輸送も、点ごとの余極限性を保つ。 -/
lemma pointwiseColimitCocone_diagramEq {J K X : SSet.{u}}
    {p q : J ⟶ (ihom K).obj X} (h : p = q) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p)
    (hc : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.IsPointwiseColimitCone c) :
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.IsPointwiseColimitCone (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentCoconeOfDiagramEq h c) := by
  cases h
  exact hc

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
