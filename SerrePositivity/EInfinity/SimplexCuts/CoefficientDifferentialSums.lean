module

public import SerrePositivity.EInfinity.SimplexCuts.CoefficientBoundarySums

/-!
# 元の線形係数微分と同じ全係数境界和

Berger–Fresse §1.2.3・§2.2.7、M14 L09の証明分割。
既存のfinCongrで同じ削除位置を移し、元の線形微分の像へ全有限和をまとめる。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory SerrePositivity.TensorPowers
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- C297：同じ全係数境界和は、元の線形削除微分の像の負号。 -/
lemma sum_coefficientBoundaryTerm_succ (S : SSet.{0}) {r d q : ℕ}
    (w : Surjection.BasisWord (r + 1) (d + 1)) (x : S _⦋q⦌)
    (h : -((d + q : ℕ) : ℤ) = -(((d + 1) + q : ℕ) : ℤ) + 1) :
    (∑ c : CoefficientBoundaryIndex r (d + 1) q,
      coefficientBoundaryTerm A S r (d + 1) q w c x) =
      -((eqToHom (congrArg (fun z : ℤ => (power (chains A S) (r + 1)).X z) h)).hom
        (rawComponent A S r d q
          (Surjection.differential A (r + 1) d
            (Surjection.basis A (r + 1) (d + 1) (ULift.up w)))
          (ModuleCat.freeMk (ULift.up x)))) := by
  have he : (r + 1) + (d + 1) = r + d + 2 := by omega
  have hr := (finCongr he).sum_comp
    (fun p : Fin (r + d + 2) => ∑ s : Cut (r + d) q,
      coefficientBoundaryTerm A S r (d + 1) q w (p, s) x)
  rw [Fintype.sum_prod_type]
  trans ∑ i : Fin ((r + 1) + (d + 1)), ∑ s : Cut (r + d) q,
    coefficientBoundaryTerm A S r (d + 1) q w (Fin.cast he i, s) x
  · convert hr.symm using 1
    all_goals rfl
  · rw [rawComponent_differential_basis A S w x]
    simp only [map_sum, map_zsmul, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [coefficientBoundaryTerm_sum_cut A S w (Fin.cast he i) x h,
      rawComponent_generator_erase_positiveWord A S w i x]
    by_cases hv : Function.Surjective (Surjection.erase (positiveWord w).val (Fin.cast he i)) ∧
        Surjection.Nondegenerate (Surjection.erase (positiveWord w).val (Fin.cast he i))
    · simp only [dite_eq_left hv, deletionCoefficient_positiveWord, neg_smul]
    · simp only [dite_eq_right hv, map_zero, smul_zero, neg_zero]

/-- C298：係数次数零の全係数境界和は、元の定義のまま零。 -/
lemma sum_coefficientBoundaryTerm_zero (S : SSet.{0}) {r q : ℕ}
    (w : Surjection.BasisWord (r + 1) 0) (x : S _⦋q⦌) :
    (∑ c : CoefficientBoundaryIndex r 0 q, coefficientBoundaryTerm A S r 0 q w c x) = 0 := by
  simp only [coefficientBoundaryTerm, Finset.sum_const_zero]

/-- C299：入力次数零の全入力境界和は、元の定義のまま零。 -/
lemma sum_simplexBoundaryTerm_zero (S : SSet.{0}) {r d : ℕ}
    (w : Surjection.BasisWord (r + 1) d) (x : S _⦋0⦌) :
    (∑ c : SimplexBoundaryIndex r d 0, simplexBoundaryTerm A S w 0 c x) = 0 := by
  simp only [simplexBoundaryTerm, Finset.sum_const_zero]

end SerrePositivity.EInfinity.SimplexCuts
