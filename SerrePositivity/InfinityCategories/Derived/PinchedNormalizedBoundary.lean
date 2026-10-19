module
public import SerrePositivity.InfinityCategories.Derived.PinchedNormalizedFaces
public import SerrePositivity.HomotopicalAlgebra.Simplicial.BoundaryGluing

/-! # 正規化した差を零面に持つ実 pinched 境界

概要：零面に指定された正規化単体を置き、他の全ての面を零として境界を貼り合わせる。
方針：各面の境界は零なので、通常の全面互換性をそのまま満たす。
規約：正次元の正規化単体を入力する。使われ方：指定原始元による一段高い充填。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.PinchedHom SSet
open scoped Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] {x y : D}

/-- 零面だけに正規化した単体を置く、実際の面写像の族。 -/
def pinchedNormalizedBoundaryFace {n : ℕ} (z : LinearSimplex A x y (n + 1))
    (j : Fin (n + 3)) : (Δ[n + 1] : SSet.{max u v}) ⟶ DGNerve.pinchedHom A D x y :=
  SSet.yonedaEquiv.symm ((if j = 0 then z else 0).toPinched)

/-- 指定した全ての面の、さらに各面への制限は零。 -/
lemma pinchedNormalizedBoundaryFace_lower {n : ℕ} (z : LinearSimplex A x y (n + 1))
    (hz : ∀ J k (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)), J ≠ Finset.univ →
      z.val.component J k hJ hk = 0) (j : Fin (n + 3)) (l : Fin (n + 2)) :
    SSet.stdSimplex.δ l ≫ pinchedNormalizedBoundaryFace z j =
      SSet.yonedaEquiv.symm (0 : LinearSimplex A x y n).toPinched := by
  unfold pinchedNormalizedBoundaryFace
  apply SSet.yonedaEquiv.injective
  rw [SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
  simp only [Equiv.apply_symm_apply]
  split_ifs with hj
  · exact pinchedNormalizedSimplex_face_zero z hz l
  · exact pinchedNormalizedSimplex_face_zero 0 (fun _ _ _ _ _ => rfl) l

/-- 差を零面に置いた全ての面は、境界上で互換。 -/
lemma pinchedNormalizedBoundary_compatible {n : ℕ} (z : LinearSimplex A x y (n + 1))
    (hz : ∀ J k (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)), J ≠ Finset.univ →
      z.val.component J k hJ hk = 0) :
    SimplicialModel.BoundaryGluing.StandardCompatible (pinchedNormalizedBoundaryFace z) := by
  intro j k hjk
  exact (pinchedNormalizedBoundaryFace_lower z hz j _).trans
    (pinchedNormalizedBoundaryFace_lower z hz k _).symm

/-- 指定正規化単体を零面に持つ実境界。 -/
def pinchedNormalizedBoundary {n : ℕ} (z : LinearSimplex A x y (n + 1))
    (hz : ∀ J k (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)), J ≠ Finset.univ →
      z.val.component J k hJ hk = 0) :
    (∂Δ[n + 2] : SSet.{max u v}) ⟶ DGNerve.pinchedHom A D x y :=
  SimplicialModel.BoundaryGluing.standardDesc (pinchedNormalizedBoundaryFace z)
    (pinchedNormalizedBoundary_compatible z hz)

/-- 貼り合わせた実境界の各面は、指定した族に厳密に一致。 -/
lemma pinchedNormalizedBoundary_face {n : ℕ} (z : LinearSimplex A x y (n + 1))
    (hz : ∀ J k (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)), J ≠ Finset.univ →
      z.val.component J k hJ hk = 0) (j : Fin (n + 3)) :
    SSet.boundary.ι j ≫ pinchedNormalizedBoundary z hz = pinchedNormalizedBoundaryFace z j :=
  SimplicialModel.BoundaryGluing.standardDesc_fac _ _ j

/-- 実境界から回収した面の線形データも指定した族に一致。 -/
lemma pinchedNormalizedBoundary_faceData {n : ℕ} (z : LinearSimplex A x y (n + 1))
    (hz : ∀ J k (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)), J ≠ Finset.univ →
      z.val.component J k hJ hk = 0) (j : Fin (n + 3)) :
    pinchedBoundaryFaceData (pinchedNormalizedBoundary z hz) j = if j = 0 then z.val else 0 := by
  unfold pinchedBoundaryFaceData
  rw [pinchedNormalizedBoundary_face]
  change (toLinearSimplex (SSet.yonedaEquiv (pinchedNormalizedBoundaryFace z j))).val = _
  simp only [pinchedNormalizedBoundaryFace, Equiv.apply_symm_apply,
    LinearSimplex.toLinearSimplex_toPinched]
  split_ifs <;> rfl

end SerrePositivity.InfinityCategories
