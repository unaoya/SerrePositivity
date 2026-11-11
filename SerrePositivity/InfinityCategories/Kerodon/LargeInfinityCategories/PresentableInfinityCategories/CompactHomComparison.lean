module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.HomComparison
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.HomComparisonColimitClass
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AccessibleFunctor
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.UniverseCoconePostcomposition

/-!
概要：元の全共変 Hom 比較の可逆成分を、compact 性で小さい filtered 余極限へ拡張。
方針：両側の同じ全 Hom による保存と、指定余錐の宇宙・後合成の一致を使う。
規約：κ と添字は u、圏は u+1。元の全比較と元の余錐を固定する。
使われ方：Ind 比較の生成対象から任意の Ind 対象への拡張。

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

/-- compact な始点とその像の同じ全 Hom 比較は、元の filtered 余極限頂点へ延長する。 -/
lemma covariantHomComparison_component_colimit {κ : Cardinal.{u}}
    {C E : SSet.{u + 1}} [Quasicategory C] [Quasicategory E]
    (G : C ⟶ E) (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ G) (x : C _⦋0⦌)
    (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} κ x)
    (hGx : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} κ (G.app (Opposite.op ⦋0⦌) x))
    {I : SSet.{u}} [Quasicategory I] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ I]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ C) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
    (ht : ∀ j : I _⦋0⦌, IsIso ((hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
      (X := (SSet.uliftFunctor.{u + 2, u + 1}).obj C) (Y := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u + 1})
      (ULift.up (D.app (Opposite.op ⦋0⦌) (ULift.up j))))).toFunctor.map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.covariantHomComparison G x))) :
    IsIso ((hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
      (X := (SSet.uliftFunctor.{u + 2, u + 1}).obj C) (Y := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u + 1})
      (ULift.up c.vertex))).toFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.covariantHomComparison G x)) := by
  have hF := hx I D c hc
  have hT : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone
      ((SSet.uliftFunctor.{u + 2, u + 1}).map G ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.covariantRepresentableInfinity (G.app (Opposite.op ⦋0⦌) x)) (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCocone.ulift c)) := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.mapJoinCocone_universe_comp]
    exact hGx I (D ≫ G) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone G c) (hG I D c hc)
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorHomComparison_colimit_vertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCocone.ulift c)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.covariantHomComparison G x) hF hT (by
      rintro ⟨⟨j⟩⟩
      exact ht j)
  have hv : (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCocone.ulift.{u + 1, u + 2} c).vertex = ULift.up c.vertex :=
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCocone.ulift_vertex c
  rw [hv] at h
  exact h

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
