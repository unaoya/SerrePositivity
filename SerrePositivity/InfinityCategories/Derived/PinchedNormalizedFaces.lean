module
public import SerrePositivity.InfinityCategories.Derived.PinchedTopComparison
public import SerrePositivity.InfinityCategories.Derived.PinchedBoundaryData

/-! # 正規化した pinched 単体の全ての面

概要：全真部分集合の成分が零なら、実際の全ての面も零単体になる。
方針：余面の部分集合像は真部分集合であり、線形表示は引き戻しと可換する。
規約：正次元を扱う。使われ方：最上位の差の正規化された零ホモトピー境界。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.PinchedHom SSet
open scoped Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] {x y : D}

/-- 真部分集合で零の線形単体は、各面への引き戻しが零。 -/
lemma pinchedLinearSimplex_face_zero {n : ℕ} (z : LinearSimplex A x y (n + 1))
    (hz : ∀ J k (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)), J ≠ Finset.univ →
      z.val.component J k hJ hk = 0) (j : Fin (n + 2)) :
    LinearSimplex.pullback j.succAboveOrderEmb.toOrderHom z = 0 := by
  apply Subtype.ext
  funext i
  rcases i with ⟨⟨J, k⟩, hJ, hk⟩
  change (LinearData.pullback j.succAboveOrderEmb.toOrderHom z.val).component J k hJ hk = 0
  rw [LinearData.pullback_component_of_inj _ _ _ _ _ _ j.succAboveOrderEmb.injective.injOn]
  exact hz _ _ _ _ (pinchedBoundary_image_ne_univ j J)

/-- 真部分集合で零の線形単体から戻した実 pinched 単体の全ての面は零。 -/
lemma pinchedNormalizedSimplex_face_zero {n : ℕ} (z : LinearSimplex A x y (n + 1))
    (hz : ∀ J k (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)), J ≠ Finset.univ →
      z.val.component J k hJ hk = 0) (j : Fin (n + 2)) :
    z.toPinched.pullback (SimplexCategory.δ j) = (0 : LinearSimplex A x y n).toPinched := by
  apply (linearEquiv x y n).injective
  change toLinearSimplex (z.toPinched.pullback (SimplexCategory.δ j)) =
    toLinearSimplex (0 : LinearSimplex A x y n).toPinched
  rw [toLinearSimplex_pullback, LinearSimplex.toLinearSimplex_toPinched,
    LinearSimplex.toLinearSimplex_toPinched]
  exact pinchedLinearSimplex_face_zero z hz j

/-- 最上位比較の差の全ての実面は零。 -/
lemma PinchedTopComparison.difference_face_zero {n : ℕ} {s t : LinearSimplex A x y (n + 1)}
    (c : PinchedTopComparison s t) (j : Fin (n + 2)) :
    (s - t).toPinched.pullback (SimplexCategory.δ j) =
      (0 : LinearSimplex A x y n).toPinched :=
  pinchedNormalizedSimplex_face_zero (s - t) c.difference_proper_zero j

end SerrePositivity.InfinityCategories
