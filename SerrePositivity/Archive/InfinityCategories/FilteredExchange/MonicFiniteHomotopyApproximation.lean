module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.MonicAnchoredFiniteApproximation
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CylinderBoundaryMono

/-!
概要：指定された有限ホモトピーを、単射な両端境界を持つ有限模型で近似する。
方針：両端の直和の単射な包含に、境界固定の有限写像円柱補正を適用する。
規約：元の path との比較ホモトピーは両端上で時間に定値。
使われ方：Kan 引き戻しの指定 path を底上の相対持ち上げへ渡す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：元の有限二射を結ぶ指定 path を、両端が単射な有限模型に移せる。
方針：全円柱を有限相対射として近似し、元の両端を比較の全時刻で固定する。
規約：指定 path 自体への実ホモトピーを保持。使われ方：標的の三座標の同時有限検出。 -/
lemma continuousKanReplacement_homotopy_monic_finite_approximation {K E : SSet.{u}}
    [K.Finite] (f₀ f₁ : K ⟶ E)
    (H : SSet.Homotopy (f₀ ≫ continuousKanReplacementUnit.app E)
      (f₁ ≫ continuousKanReplacementUnit.app E)) :
    ∃ (M : SSet.{u}) (m : K ⨿ K ⟶ M) (q : M ⟶ E)
      (v : K ⊗ (Δ[1] : SSet.{u}) ⟶ continuousKanReplacement.obj M),
      M.Finite ∧ Mono m ∧ m ≫ q = coprod.desc f₀ f₁ ∧
      cylinderBoundaryInclusion K ≫ v = m ≫ continuousKanReplacementUnit.app M ∧
      ∃ G : SSet.Homotopy H.h (v ≫ continuousKanReplacement.map q),
        (cylinderBoundaryInclusion K ▷ (Δ[1] : SSet.{u})) ≫ G.h =
          fst (K ⨿ K) (Δ[1] : SSet.{u}) ≫ coprod.desc f₀ f₁ ≫
            continuousKanReplacementUnit.app E := by
  have h : coprod.desc f₀ f₁ ≫ continuousKanReplacementUnit.app E =
      cylinderBoundaryInclusion K ≫ H.h := by
    apply coprod.hom_ext
    · rw [← Category.assoc, coprod.inl_desc, cylinderBoundaryInclusion,
        ← Category.assoc, coprod.inl_desc]
      exact H.h₀.symm
    · rw [← Category.assoc, coprod.inr_desc, cylinderBoundaryInclusion,
        ← Category.assoc, coprod.inr_desc]
      exact H.h₁.symm
  exact continuousKanReplacement_monic_anchored_finite_approximation
    (cylinderBoundaryInclusion K) (coprod.desc f₀ f₁) H.h h

end SerrePositivity.InfinityCategories.F2
