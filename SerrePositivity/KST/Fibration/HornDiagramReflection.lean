module
public import SerrePositivity.KST.Fibration.ComposableWeakArrows
public import Mathlib.CategoryTheory.Limits.Types.Pushouts

/-! # 内二ホーン上の図式の両短辺による零対象・押し出しの反映 -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration

/-- 内二ホーンの全頂点は元の二短辺のどちらかに属する。 -/
lemma innerTwoHorn_vertex_cover (v : (Λ[2, 1] : SSet.{u}) _⦋0⦌) :
    (∃ a, horn₂₁.ι₀₁.app (Opposite.op ⦋0⦌) a = v) ∨
      ∃ a, horn₂₁.ι₁₂.app (Opposite.op ⦋0⦌) a = v := by
  exact Types.eq_or_eq_of_isPushout
    (horn₂₁.isPushout.{u}.map
      ((evaluation SimplexCategoryᵒᵖ (Type u)).obj (Opposite.op ⦋0⦌))) v

/-- 全ホーン図式の両短辺が零対象なら、元の図式も零対象。 -/
lemma innerTwoHorn_isZeroVertex_of_edges {B : SSet.{u}} [Quasicategory B]
    [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex B] (v : ((ihom (Λ[2, 1] : SSet.{u})).obj B) _⦋0⦌)
    (h₀ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (((pre horn₂₁.ι₀₁).app B).app (Opposite.op ⦋0⦌) v))
    (h₁ : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (((pre horn₂₁.ι₁₂).app B).app (Opposite.op ⦋0⦌) v)) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex v := by
  apply isZeroVertex_of_pointwise
  intro k
  obtain (⟨a, rfl⟩ | ⟨a, rfl⟩) := innerTwoHorn_vertex_cover k
  · have h := isZeroVertex_evaluateFunctorAt h₀ a
    change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (((pre horn₂₁.ι₀₁).app B ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a).app _ v) at h
    rwa [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.stable_pre_evaluateFunctorAt] at h
  · have h := isZeroVertex_evaluateFunctorAt h₁ a
    change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex (((pre horn₂₁.ι₁₂).app B ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a).app _ v) at h
    rwa [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.stable_pre_evaluateFunctorAt] at h

/-- 全ホーン図式の実正方形は、両短辺で押し出しなら元も押し出し。 -/
lemma innerTwoHorn_isPushoutSquare_of_edges {B : SSet.{u}} [Quasicategory B] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable B]
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ (ihom (Λ[2, 1] : SSet.{u})).obj B)
    (h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (F ≫ (pre horn₂₁.ι₀₁).app B))
    (h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (F ≫ (pre horn₂₁.ι₁₂).app B)) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare F := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isPushoutSquare_of_pointwise
  intro k
  obtain (⟨a, rfl⟩ | ⟨a, rfl⟩) := innerTwoHorn_vertex_cover k
  · have h := (evaluateFunctorAt_preservesSConstructionData (C := B) a).2 _ h₀
    rwa [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.stable_pre_evaluateFunctorAt] at h
  · have h := (evaluateFunctorAt_preservesSConstructionData (C := B) a).2 _ h₁
    rwa [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.stable_pre_evaluateFunctorAt] at h

end SerrePositivity.KST.Fibration
