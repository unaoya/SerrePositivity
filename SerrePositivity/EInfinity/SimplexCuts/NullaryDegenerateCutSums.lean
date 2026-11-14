module

public import SerrePositivity.EInfinity.SimplexCuts.DegenerateCutGeneratorFamilies
public import SerrePositivity.EInfinity.SimplexCuts.CochainNullaryInsertionDegrees
public import SerrePositivity.EInfinity.SimplexCuts.NullaryZeroColor

/-!
# 退化raw削除語の実際の空語二段作用の全和の零性

Berger–Fresse §2.2.6・§3.1、M14 L12a、報告 §361。
正次数の内側出力と、退化する元の零次Cutを別々に零として全和を保つ。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
open scoped Simplicial

/-- 退化raw削除語に対する元の空語二段作用の全Cut和は零（BF §2.2.6）。 -/
lemma sum_nullary_cochain_cut_terms_of_raw_degenerate
    (A : Type u) [CommRing A] (S : SSet.{0}) {m q r : ℕ}
    (v : Surjection.Word (r + 1) (m + 2)) (w : Fin (m + 1) → Fin r)
    (p : Fin (m + 2)) (k : Fin (r + 1)) (hp : v.val p = k)
    (hv : ∀ i, k.succAbove (w i) = v.val (p.succAbove i))
    (hw : ¬Surjection.Nondegenerate w) (ν : Surjection.BasisWord 0 0)
    (x : S _⦋q⦌) (z : ℤ) (hz : -((m + q + 1 - r : ℕ) : ℤ) = z) :
    (∑ s : Cut (m + 1) q, cutSign s v.val •
      (tensorCoInsertionAction (chains A S) (Surjection.complex A 0) r 0 k
        (cochainAction A S 0)).f z
        (ιTensorObj (Surjection.complex A 0) (power (chains A S) (r + 1)) 0 z z (zero_add z)
          ((Surjection.complexXIso A 0 0).inv (Surjection.basis A 0 0 (ULift.up ν)) ⊗ₜ[A]
            vectorTensorAt (chains A S) (r + 1) (cutGeneratorFamily A S s v x) z
              (by rw [vectorDegree_cutGeneratorFamily]
                  have h : (m + 1) + q + 1 - (r + 1) = m + q + 1 - r := by omega
                  rwa [h])))) = 0 := by
  have houter (s : Cut (m + 1) q) :
      -(vectorDegree (chains A S) (r + 1) (cutGeneratorFamily A S s v x) : ℤ) = z := by
    rw [vectorDegree_cutGeneratorFamily]
    have h : (m + 1) + q + 1 - (r + 1) = m + q + 1 - r := by omega
    rwa [h]
  apply Finset.sum_eq_zero
  intro s _
  by_cases hzero : outputDegree s v k = 0
  · have hpoint := outputDegree_zero_hi_eq_lo s v k hzero p hp
    have hcut := not_nondegenerate_of_nullary_raw_degenerate s v w p k hpoint hv hw
    have H := vectorTensorAt_cutGeneratorFamily_eq_zero A S s v x hcut z (houter s)
    simp only [H, TensorProduct.tmul_zero, map_zero, smul_zero]
  · have hpos : 0 < (cutGeneratorFamily A S s v x k).1 := Nat.pos_of_ne_zero hzero
    have H := tensorCoInsertionAction_cochain_nullary_positive_at A S ν k
      (cutGeneratorFamily A S s v x) hpos z z (houter s) (zero_add z)
    exact (congrArg (fun y => cutSign s v.val • y) H).trans (smul_zero _)

end SerrePositivity.EInfinity.SimplexCuts
