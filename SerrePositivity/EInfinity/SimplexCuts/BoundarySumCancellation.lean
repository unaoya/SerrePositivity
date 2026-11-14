module

public import SerrePositivity.EInfinity.SimplexCuts.BoundaryPairingValues

/-!
# BF全境界項の有限和の相殺

Berger–Fresse §2.2.7、M14 L09の証明分割。
同じ対合と固定点の零を既存の有限和の相殺則に適用する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory SerrePositivity.TensorPowers
open scoped Simplicial

/-- C256：同じ実境界値の全有限和は、元の加群で零となる。 -/
lemma sum_boundaryBalanceTerm_eq_zero (A : Type u) [CommRing A] (S : SSet.{0}) {r d : ℕ}
    (w : Surjection.BasisWord (r + 1) d) (q : ℕ) (x : S _⦋q⦌) :
    ∑ i : BoundaryBalanceIndex w q, boundaryBalanceTerm A S w q i x = 0 := by
  classical
  apply Finset.sum_ninvolution (boundaryBalancePerm w q)
  · intro i
    rw [boundaryBalancePerm_neg A S w q x i]
    exact add_neg_cancel _
  · intro i hne he
    exact hne (boundaryBalancePerm_fixed_zero A S w q i he x)
  · intro i
    exact Finset.mem_univ _
  · exact boundaryBalancePerm_involutive w q

end SerrePositivity.EInfinity.SimplexCuts
