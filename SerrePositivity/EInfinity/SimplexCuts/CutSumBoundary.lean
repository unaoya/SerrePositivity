module

public import SerrePositivity.EInfinity.SimplexCuts.CutSumBoundaryInputs
public import SerrePositivity.EInfinity.SimplexCuts.OutputBoundarySums

/-!
# 同じ一般のBF切断和の微分

Berger–Fresse §1.2.3・§2.2.7、M14 L09。
全境界項の相殺を、元の線形削除微分と元の正規化鎖微分の像へ戻す。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory SerrePositivity.TensorPowers
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- L09：同じ切断和は、零次数も含めて元の二つの微分のLeibniz則を満たす。 -/
theorem cutSum_boundary (S : SSet.{0}) {r d q : ℕ}
    (w : Surjection.BasisWord (r + 1) d) (x : S _⦋q⦌) :
    (power (chains A S) (r + 1)).d (-((d + q : ℕ) : ℤ))
        (-((d + q : ℕ) : ℤ) + 1) (cutSum A S w x) =
      cutSumCoefficientBoundary A S r d q w x +
        (-1 : ℤ) ^ d • cutSumSimplexBoundary A S w q x := by
  rw [cutSum_d_eq_neg_boundarySums, sum_coefficientBoundaryTerm_eq, sum_simplexBoundaryTerm_eq]
  simp only [neg_smul]
  abel

end SerrePositivity.EInfinity.SimplexCuts
