module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.HomComparisonComponent
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CompactHomComparison

/-!
概要：compact な始点とその像について、実写像空間比較の同値性を filtered 余極限へ拡張。
方針：全自然な Hom 比較の成分判定と、同じ指定余錐上の compact 保存性を合成する。
規約：元の pinchedHomMap 自身の同値性。標的の全充満忠実性は仮定しない。
使われ方：Ind 比較の Yoneda 生成対象から任意対象への写像空間比較。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 同じ元の κ-filtered 表示の各項での比較同値性は、compact 性により頂点へ延長。 -/
lemma pinchedHomMap_equivalence_of_compact_colimit {κ : Cardinal.{u}}
    {C E : SSet.{u + 1}} [Quasicategory C] [Quasicategory E]
    (G : C ⟶ E) (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ G) (x : C _⦋0⦌)
    (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} κ x)
    (hGx : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} κ (G.app (Opposite.op ⦋0⦌) x))
    {I : SSet.{u}} [Quasicategory I] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ I]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ C) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
    (ht : ∀ j : I _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap G x (D.app (Opposite.op ⦋0⦌) (ULift.up j)))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap G x c.vertex) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.covariantHomComparison_component_isIso_iff G x c.vertex).mp
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.covariantHomComparison_component_colimit G hG x hx hGx D c hc
  intro j
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.covariantHomComparison_component_isIso_iff G x _).mpr (ht j)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
