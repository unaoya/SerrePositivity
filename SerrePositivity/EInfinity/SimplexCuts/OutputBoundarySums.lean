module

public import SerrePositivity.EInfinity.SimplexCuts.CutTermDifferential
public import SerrePositivity.EInfinity.SimplexCuts.BoundarySumCancellation

/-!
# 同じ切断和の微分と全実境界項

Berger–Fresse §2.2.7、M14 L09の証明分割。
切断ごとの微分則と全境界項の相殺を、同じ共通次数での切断和へ戻す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory SerrePositivity.TensorPowers
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- C258：同じ切断和の微分は、同じ指定出力境界値を移送した全和。 -/
lemma cutSum_d_eq_sum_outputBoundaryTerm (S : SSet.{0})
    {r d q : ℕ} (w : Surjection.BasisWord (r + 1) d) (x : S _⦋q⦌)
    (h : -((r + d + q + 1 - (r + 1) : ℕ) : ℤ) + 1 = -((d + q : ℕ) : ℤ) + 1) :
    (power (chains A S) (r + 1)).d (-((d + q : ℕ) : ℤ))
        (-((d + q : ℕ) : ℤ) + 1) (cutSum A S w x) =
      ∑ s : Cut (r + d) q, ∑ a : Fin (r + 1),
        ∑ j : Fin (outputDegree s (positiveWord w) a + 1),
          (eqToHom (congrArg (fun z : ℤ => (power (chains A S) (r + 1)).X z) h)).hom
            (outputBoundaryTerm A S s (positiveWord w) a j x) := by
  have h0 : -((r + d + q + 1 - (r + 1) : ℕ) : ℤ) = -((d + q : ℕ) : ℤ) := by omega
  have hc := complex_d_cast_source_target A (power (chains A S) (r + 1))
    (i := -((r + d + q + 1 - (r + 1) : ℕ) : ℤ)) (i' := -((d + q : ℕ) : ℤ))
    (j := -((r + d + q + 1 - (r + 1) : ℕ) : ℤ) + 1) (j' := -((d + q : ℕ) : ℤ) + 1)
    h0 h (∑ s : Cut (r + d) q, cutTerm A S s (positiveWord w) x)
  simp only [map_sum, cutTerm_d_eq_sum_outputBoundaryTerm] at hc
  unfold cutSum
  simp only [map_sum]
  convert hc using 1

/-- C282：全出力境界項の同じ有限和は、元のcutSumの微分。 -/
lemma sum_boundaryBalanceTerm_output_eq_d_cutSum (S : SSet.{0}) {r d : ℕ}
    (w : Surjection.BasisWord (r + 1) d) (q : ℕ) (x : S _⦋q⦌) :
    (∑ i : OutputBoundaryIndex w q, boundaryBalanceTerm A S w q (.inl i) x) =
      (power (chains A S) (r + 1)).d (-((d + q : ℕ) : ℤ))
        (-((d + q : ℕ) : ℤ) + 1) (cutSum A S w x) := by
  rw [cutSum_d_eq_sum_outputBoundaryTerm A S w x (by omega)]
  simp only [Fintype.sum_sigma, boundaryBalanceTerm]

/-- C283：同じcutSumの微分は、残る二つの元の実境界和の和の負号。 -/
lemma cutSum_d_eq_neg_boundarySums (S : SSet.{0}) {r d : ℕ}
    (w : Surjection.BasisWord (r + 1) d) (q : ℕ) (x : S _⦋q⦌) :
    (power (chains A S) (r + 1)).d (-((d + q : ℕ) : ℤ))
        (-((d + q : ℕ) : ℤ) + 1) (cutSum A S w x) =
      -((∑ c : CoefficientBoundaryIndex r d q, coefficientBoundaryTerm A S r d q w c x) +
        ∑ i : SimplexBoundaryIndex r d q, simplexBoundaryTerm A S w q i x) := by
  have ht := sum_boundaryBalanceTerm_eq_zero A S w q x
  simp only [Fintype.sum_sum_type] at ht
  rw [sum_boundaryBalanceTerm_output_eq_d_cutSum A S w q x] at ht
  change (power (chains A S) (r + 1)).d (-((d + q : ℕ) : ℤ))
      (-((d + q : ℕ) : ℤ) + 1) (cutSum A S w x) +
      ((∑ c : CoefficientBoundaryIndex r d q, coefficientBoundaryTerm A S r d q w c x) +
        ∑ i : SimplexBoundaryIndex r d q, simplexBoundaryTerm A S w q i x) = 0 at ht
  exact eq_neg_of_add_eq_zero_left ht

end SerrePositivity.EInfinity.SimplexCuts
