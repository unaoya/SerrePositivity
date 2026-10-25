module
public import SerrePositivity.InfinityCategories.Derived.DGCoherentBarShiftedInclusions

/-!
概要：θ を各元の単体の符号付き包含に合成した式を、面と prefix の一次の和へ展開する。
方針：元の列の有限和へ合成を分配し、二つの次元符号を消去する。
規約：同じ θ と全単体ラベルを使い、MC 方程式を仮定しない。
使われ方：Bianchi の HA 右辺の有限和との直接比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial

private lemma signedColumn_comp {A : Type u} [CommRing A] {C : Type v} [DGCategory A C]
    {M S B : C} {p : ℤ} (n : ℤ) (m : ℕ) (f g : Fin m → GradedHom A S B 1)
    (e : GradedHom A M S p) :
    n.negOnePow • compose A
      ((∑ i, (n + (i.val : ℤ) + 1).negOnePow • f i) + n.negOnePow • ∑ i, g i) e rfl =
      (∑ i, ((i.val : ℤ) + 1).negOnePow • compose A (f i) e rfl) +
        ∑ i, compose A (g i) e rfl := by
  simp only [compose_add_left, compose_sum_left, compose_units_smul_left,
    smul_add, Finset.smul_sum, smul_smul, Int.units_mul_self, one_smul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have hs : n.negOnePow * (n + (i.val : ℤ) + 1).negOnePow =
      ((i.val : ℤ) + 1).negOnePow := by
    rw [← Int.negOnePow_add]
    have hi : n + (n + (i.val : ℤ) + 1) = 2 * n + ((i.val : ℤ) + 1) := by ring
    rw [hi, Int.negOnePow_add, Int.negOnePow_two_mul, one_mul]
  rw [hs]

variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

def dgCoherentBarUnshiftedBoundary {n : ℕ} (σ : I _⦋n + 1⦌) :
    GradedHom R (dgCoherentBarSource R D F ⟨n + 1, σ⟩)
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F)) (-((n + 1 : ℕ) : ℤ) + 1) :=
  (∑ i : Fin (n + 1), ((i.val : ℤ) + 1).negOnePow •
    compose R (x := dgCoherentBarSource R D F ⟨n + 1, σ⟩)
      (y := ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨n + 1, σ⟩))
      (z := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (dgCoherentBarFaceColumn R D F σ i)
      (moduleShiftInElement R D ((n + 1 : ℕ) : ℤ) (dgCoherentBarSource R D F ⟨n + 1, σ⟩)) rfl) +
  ∑ k : Fin (n + 1), compose R (x := dgCoherentBarSource R D F ⟨n + 1, σ⟩)
    (y := ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨n + 1, σ⟩))
    (z := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
    (dgCoherentBarPrefixColumn R D F σ k.val (by omega))
    (moduleShiftInElement R D ((n + 1 : ℕ) : ℤ) (dgCoherentBarSource R D F ⟨n + 1, σ⟩)) rfl


def dgCoherentBarUnshiftedBoundaryTerm {n : ℕ} (σ : I _⦋n + 1⦌) (i : Fin (n + 1)) :
    GradedHom R (dgCoherentBarSource R D F ⟨n + 1, σ⟩)
      (ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F)) (-((n + 1 : ℕ) : ℤ) + 1) :=
  ((i.val : ℤ) + 1).negOnePow •
    compose R (x := dgCoherentBarSource R D F ⟨n + 1, σ⟩)
      (y := ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨n + 1, σ⟩))
      (z := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (dgCoherentBarFaceColumn R D F σ i)
      (moduleShiftInElement R D ((n + 1 : ℕ) : ℤ) (dgCoherentBarSource R D F ⟨n + 1, σ⟩)) rfl +
  compose R (x := dgCoherentBarSource R D F ⟨n + 1, σ⟩)
    (y := ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨n + 1, σ⟩))
    (z := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
    (dgCoherentBarPrefixColumn R D F σ i.val (by omega))
    (moduleShiftInElement R D ((n + 1 : ℕ) : ℤ) (dgCoherentBarSource R D F ⟨n + 1, σ⟩)) rfl

lemma dgCoherentBarUnshiftedBoundary_eq_sum_terms {n : ℕ} (σ : I _⦋n + 1⦌) :
    dgCoherentBarUnshiftedBoundary R D F σ =
      ∑ i : Fin (n + 1), dgCoherentBarUnshiftedBoundaryTerm R D F σ i := by
  unfold dgCoherentBarUnshiftedBoundary dgCoherentBarUnshiftedBoundaryTerm
  rw [Finset.sum_add_distrib]

lemma dgCoherentBarTheta_comp_shiftedInclusion_positive {n : ℕ} (σ : I _⦋n + 1⦌) :
    compose R (x := dgCoherentBarSource R D F ⟨n + 1, σ⟩)
      (y := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (z := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (dgCoherentBarTheta R D F) (dgCoherentBarShiftedInclusion R D F ⟨n + 1, σ⟩) rfl =
      dgCoherentBarUnshiftedBoundary R D F σ := by
  rw [dgCoherentBarTheta_comp_shiftedInclusion R D F]
  exact signedColumn_comp (A := R) (C := RightModule R D)
    (M := dgCoherentBarSource R D F ⟨n + 1, σ⟩)
    (S := ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨n + 1, σ⟩))
    (B := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
    ((n + 1 : ℕ) : ℤ) (n + 1) (dgCoherentBarFaceColumn R D F σ)
    (fun k => dgCoherentBarPrefixColumn R D F σ k.val (by omega))
    (moduleShiftInElement R D ((n + 1 : ℕ) : ℤ) (dgCoherentBarSource R D F ⟨n + 1, σ⟩))

end SerrePositivity.InfinityCategories
