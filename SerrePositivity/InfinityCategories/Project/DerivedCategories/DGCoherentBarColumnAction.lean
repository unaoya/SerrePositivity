module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGCoherentBarShiftedInclusions

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial

private lemma signedColumn_comp {A : Type u} [CommRing A] {C : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A C]
    {M S B : C} {p : ℤ} (n : ℤ) (m : ℕ) (f g : Fin m → _root_.SerrePositivity.DifferentialGraded.GradedHom A S B 1)
    (e : _root_.SerrePositivity.DifferentialGraded.GradedHom A M S p) :
    n.negOnePow • _root_.SerrePositivity.DifferentialGraded.compose A
      ((∑ i, (n + (i.val : ℤ) + 1).negOnePow • f i) + n.negOnePow • ∑ i, g i) e rfl =
      (∑ i, ((i.val : ℤ) + 1).negOnePow • _root_.SerrePositivity.DifferentialGraded.compose A (f i) e rfl) +
        ∑ i, _root_.SerrePositivity.DifferentialGraded.compose A (g i) e rfl := by
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_add_left, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_sum_left, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_units_smul_left,
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

variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

def dgCoherentBarUnshiftedBoundary {n : ℕ} (σ : I _⦋n + 1⦌) :
    GradedHom R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨n + 1, σ⟩)
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F)) (-((n + 1 : ℕ) : ℤ) + 1) :=
  (∑ i : Fin (n + 1), ((i.val : ℤ) + 1).negOnePow •
    compose R (x := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨n + 1, σ⟩)
      (y := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨n + 1, σ⟩))
      (z := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFaceColumn R D F σ i)
      (moduleShiftInElement R D ((n + 1 : ℕ) : ℤ) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨n + 1, σ⟩)) rfl) +
  ∑ k : Fin (n + 1), compose R (x := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨n + 1, σ⟩)
    (y := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨n + 1, σ⟩))
    (z := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixColumn R D F σ k.val (by omega))
    (moduleShiftInElement R D ((n + 1 : ℕ) : ℤ) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨n + 1, σ⟩)) rfl


def dgCoherentBarUnshiftedBoundaryTerm {n : ℕ} (σ : I _⦋n + 1⦌) (i : Fin (n + 1)) :
    GradedHom R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨n + 1, σ⟩)
      (ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F)) (-((n + 1 : ℕ) : ℤ) + 1) :=
  ((i.val : ℤ) + 1).negOnePow •
    compose R (x := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨n + 1, σ⟩)
      (y := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨n + 1, σ⟩))
      (z := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFaceColumn R D F σ i)
      (moduleShiftInElement R D ((n + 1 : ℕ) : ℤ) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨n + 1, σ⟩)) rfl +
  compose R (x := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨n + 1, σ⟩)
    (y := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨n + 1, σ⟩))
    (z := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixColumn R D F σ i.val (by omega))
    (moduleShiftInElement R D ((n + 1 : ℕ) : ℤ) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨n + 1, σ⟩)) rfl

lemma dgCoherentBarUnshiftedBoundary_eq_sum_terms {n : ℕ} (σ : I _⦋n + 1⦌) :
    dgCoherentBarUnshiftedBoundary R D F σ =
      ∑ i : Fin (n + 1), dgCoherentBarUnshiftedBoundaryTerm R D F σ i := by
  unfold dgCoherentBarUnshiftedBoundary dgCoherentBarUnshiftedBoundaryTerm
  rw [Finset.sum_add_distrib]

lemma dgCoherentBarTheta_comp_shiftedInclusion_positive {n : ℕ} (σ : I _⦋n + 1⦌) :
    compose R (x := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨n + 1, σ⟩)
      (y := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
      (z := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTheta R D F) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarShiftedInclusion R D F ⟨n + 1, σ⟩) rfl =
      dgCoherentBarUnshiftedBoundary R D F σ := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarTheta_comp_shiftedInclusion R D F]
  exact signedColumn_comp (A := R) (C := _root_.SerrePositivity.DifferentialGraded.RightModule R D)
    (M := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨n + 1, σ⟩)
    (S := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFamily R D F ⟨n + 1, σ⟩))
    (B := ForgetEnrichment.to (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarGraded R D F))
    ((n + 1 : ℕ) : ℤ) (n + 1) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarFaceColumn R D F σ)
    (fun k => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarPrefixColumn R D F σ k.val (by omega))
    (moduleShiftInElement R D ((n + 1 : ℕ) : ℤ) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨n + 1, σ⟩))

end SerrePositivity.InfinityCategories.Project.DerivedCategories
