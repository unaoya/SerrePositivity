module
public import SerrePositivity.InfinityCategories.Derived.PinchedNormalizedFiller

/-! # 正規化した差の充填の実際の面と最上位成分

概要：指定原始元で作った一段高い単体の零面は差であり、他の面は厳密に零となる。
方針：置換で保持した全真部分集合を余面へ引き戻し、実境界の指定面を回収する。
規約：符号付き原始元そのものを最上位に持つ。使われ方：prism への貼り合わせ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.PinchedHom
open scoped Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] {x y : D}

/-- 正規化した充填の全ての線形面は、指定された差または零に一致。 -/
lemma PinchedTopComparison.normalizedFiller_pullback {n : ℕ}
    {s t : LinearSimplex A x y (n + 1)} (c : PinchedTopComparison s t) (j : Fin (n + 3)) :
    LinearSimplex.pullback j.succAboveOrderEmb.toOrderHom c.normalizedFiller =
      if j = 0 then s - t else 0 := by
  apply Subtype.ext
  change LinearData.pullback j.succAboveOrderEmb.toOrderHom c.normalizedFiller.val = _
  have hr := pinchedNormalizedBoundary_faceData (s - t) c.difference_proper_zero j
  have hp := pinchedBoundaryKnownData_pullback_face
    (pinchedNormalizedBoundary (s - t) c.difference_proper_zero) j
  rw [hr] at hp
  have ht : (if j = 0 then s - t else 0 : LinearSimplex A x y (n + 1)).val =
      if j = 0 then (s - t).val else 0 := by split_ifs <;> rfl
  rw [ht, ← hp]
  funext i
  rcases i with ⟨⟨J, k⟩, hJ, hk⟩
  let f := pinchedBoundaryKnownData
    (pinchedNormalizedBoundary (s - t) c.difference_proper_zero)
  change (LinearData.pullback j.succAboveOrderEmb.toOrderHom c.normalizedFiller.val).component
    J k hJ hk = (LinearData.pullback j.succAboveOrderEmb.toOrderHom f).component J k hJ hk
  rw [LinearData.pullback_component_of_inj _ _ _ _ _ _ j.succAboveOrderEmb.injective.injOn,
    LinearData.pullback_component_of_inj _ _ _ _ _ _ j.succAboveOrderEmb.injective.injOn]
  exact pinchedCompleteTopAtDegree_proper _ _ _ _ _ _ _ _ _ _
    (pinchedBoundary_image_ne_univ j J)

/-- 一段高い実 pinched 単体の零面は差、他の面は零。 -/
lemma PinchedTopComparison.normalizedFiller_face {n : ℕ}
    {s t : LinearSimplex A x y (n + 1)} (c : PinchedTopComparison s t) (j : Fin (n + 3)) :
    c.normalizedFiller.toPinched.pullback (SimplexCategory.δ j) =
      (if j = 0 then s - t else 0).toPinched := by
  apply (linearEquiv x y (n + 1)).injective
  change toLinearSimplex (c.normalizedFiller.toPinched.pullback (SimplexCategory.δ j)) =
    toLinearSimplex (if j = 0 then s - t else 0).toPinched
  rw [toLinearSimplex_pullback, LinearSimplex.toLinearSimplex_toPinched,
    LinearSimplex.toLinearSimplex_toPinched]
  exact c.normalizedFiller_pullback j

/-- 最上位成分は、零面の削除係数を掛けた指定原始元そのもの。 -/
lemma PinchedTopComparison.normalizedFiller_full {n : ℕ}
    {s t : LinearSimplex A x y (n + 1)} (c : PinchedTopComparison s t) :
    c.normalizedFiller.val.component Finset.univ (pinchedTopDegree (n + 1) - 1)
      Finset.univ_nonempty (by simp [pinchedTopDegree]; omega) =
        deletionSign (Finset.univ : Finset (Fin (n + 3))) 0 • c.primitive :=
  pinchedCompleteTopAtDegree_full _ _ _ _ _ _

end SerrePositivity.InfinityCategories
