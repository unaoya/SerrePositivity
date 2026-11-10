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
    [HasZeroVertex B] (v : ((ihom (Λ[2, 1] : SSet.{u})).obj B) _⦋0⦌)
    (h₀ : IsZeroVertex (((pre horn₂₁.ι₀₁).app B).app (Opposite.op ⦋0⦌) v))
    (h₁ : IsZeroVertex (((pre horn₂₁.ι₁₂).app B).app (Opposite.op ⦋0⦌) v)) :
    IsZeroVertex v := by
  apply isZeroVertex_of_pointwise
  intro k
  obtain (⟨a, rfl⟩ | ⟨a, rfl⟩) := innerTwoHorn_vertex_cover k
  · have h := isZeroVertex_evaluateFunctorAt h₀ a
    change IsZeroVertex (((pre horn₂₁.ι₀₁).app B ≫ evaluateFunctorAt a).app _ v) at h
    rwa [stable_pre_evaluateFunctorAt] at h
  · have h := isZeroVertex_evaluateFunctorAt h₁ a
    change IsZeroVertex (((pre horn₂₁.ι₁₂).app B ≫ evaluateFunctorAt a).app _ v) at h
    rwa [stable_pre_evaluateFunctorAt] at h

/-- 全ホーン図式の実正方形は、両短辺で押し出しなら元も押し出し。 -/
lemma innerTwoHorn_isPushoutSquare_of_edges {B : SSet.{u}} [Quasicategory B] [IsStable B]
    (F : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ (ihom (Λ[2, 1] : SSet.{u})).obj B)
    (h₀ : IsPushoutSquare (F ≫ (pre horn₂₁.ι₀₁).app B))
    (h₁ : IsPushoutSquare (F ≫ (pre horn₂₁.ι₁₂).app B)) : IsPushoutSquare F := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isPushoutSquare_of_pointwise
  intro k
  obtain (⟨a, rfl⟩ | ⟨a, rfl⟩) := innerTwoHorn_vertex_cover k
  · have h := (evaluateFunctorAt_preservesSConstructionData (C := B) a).2 _ h₀
    rwa [Category.assoc, stable_pre_evaluateFunctorAt] at h
  · have h := (evaluateFunctorAt_preservesSConstructionData (C := B) a).2 _ h₁
    rwa [Category.assoc, stable_pre_evaluateFunctorAt] at h

end SerrePositivity.KST.Fibration
