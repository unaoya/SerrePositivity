module
public import SerrePositivity.InfinityCategories.Derived.PinchedNormalizedBoundary
public import SerrePositivity.InfinityCategories.Derived.PinchedTopRhsFaces

/-! # 正規化した差の実境界の最上位削除右辺

概要：零面だけに差を置いた実境界の最上位右辺は、その成分の一つの符号倍。
方針：全面による右辺の式と、実境界から回収した各面の一致を使う。
規約：次数は外部から指定する。使われ方：指定原始元の符号倍による充填。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.PinchedHom
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] {x y : D}

/-- 正規化された実境界の最上位右辺は、零面の最上位成分の符号倍。 -/
lemma pinchedNormalizedBoundary_rhs {n : ℕ} (z : LinearSimplex A x y (n + 1))
    (hz : ∀ J k (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)), J ≠ Finset.univ →
      z.val.component J k hJ hk = 0)
    (k : ℤ) (hk : k = 1 - ((Finset.univ : Finset (Fin (n + 3))).card : ℤ)) :
    (pinchedBoundaryKnownData (pinchedNormalizedBoundary z hz)).rhs Finset.univ k hk =
      deletionSign (Finset.univ : Finset (Fin (n + 3))) 0 •
        z.val.component Finset.univ (k + 1) Finset.univ_nonempty (by simp at hk ⊢; omega) := by
  rw [pinchedLinearData_rhs_full_faces]
  simp_rw [pinchedBoundaryKnownData_pullback_face, pinchedNormalizedBoundary_faceData]
  rw [Finset.sum_eq_single (0 : Fin (n + 3))]
  · simp only [ite_true]
  · intro j _ hj
    rw [ite_eq_right hj]
    exact smul_zero _
  · intro h
    exact (h (Finset.mem_univ 0)).elim

end SerrePositivity.InfinityCategories
