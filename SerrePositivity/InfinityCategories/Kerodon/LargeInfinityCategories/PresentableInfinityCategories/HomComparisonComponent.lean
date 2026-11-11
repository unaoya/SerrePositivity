module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.HomClassificationInvertibility
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.HomComparisonFibers

/-!
概要：全共変 Hom 比較の指定成分の可逆性を、元の pinchedHomMap の同値性と同定する。
方針：同じ全比較の三つの指定同型と分類の端点輸送を除き、実 fiber の判定へ戻す。
規約：元の全自然な比較を保持し、値ごとに代替の比較を選ばない。
使われ方：compact 性と同じ filtered 表示による Ind 比較の生成拡張。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

private lemma isIso_map_threeIso {K : Type*} {L : Type*} [Category K] [Category L]
    (T : K ⥤ L) {A B C D E : K} (e₀ : A ≅ B) (f : B ⟶ C)
    (e₁ : D ≅ C) (e₂ : E ≅ D) :
    IsIso (T.map (e₀.hom ≫ f ≫ e₁.inv ≫ e₂.inv)) ↔ IsIso (T.map f) := by
  rw [CategoryTheory.Functor.map_comp, isIso_comp_left_iff,
    CategoryTheory.Functor.map_comp, isIso_comp_right_iff]

local instance {C D : SSet.{u}} [Quasicategory D] (G : C ⟶ D) (x : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (pullback.snd (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x ≫ G)) G) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations.pullback_snd _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x ≫ G)))⟩

/-- 同じ全共変 Hom 比較の指定成分は、同じ元の写像空間比較の同値性を検出する。 -/
lemma covariantHomComparison_component_isIso_iff {C D : SSet.{u}}
    [Quasicategory C] [Quasicategory D] (G : C ⟶ D) (x y : C _⦋0⦌) :
    IsIso ((hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
      (X := (SSet.uliftFunctor.{u + 1, u}).obj C) (Y := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
      (ULift.up y))).toFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.covariantHomComparison G x)) ↔
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap G x y) := by
  let p := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x)
  let q := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x ≫ G)
  exact (isIso_map_threeIso (hoFunctor.map
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (X := (SSet.uliftFunctor.{u + 1, u}).obj C)
      (Y := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (ULift.up y))).toFunctor
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.covariantRepresentableInfinity_cosliceIso x)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftClassificationHom p (pullback.snd q G) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.cosliceComparisonOver G x)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.cosliceComparisonOver_projection G x))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagram_baseChangeIso q G)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.covariantHomTargetCosliceIso G x).precomp ((SSet.uliftFunctor.{u + 1, u}).map G))).trans
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftClassificationHom_evaluation_isIso_iff _ _ _ _ y).trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.cosliceComparisonOver_fiber_equivalence_iff G x y))

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
