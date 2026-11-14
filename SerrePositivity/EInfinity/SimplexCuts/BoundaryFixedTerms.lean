module

public import SerrePositivity.EInfinity.SimplexCuts.BoundaryPartnerFixedPoints
public import SerrePositivity.EInfinity.SimplexCuts.BoundaryTerms

/-!
# 全境界の対合の固定点での零

Berger–Fresse §2.2.7、M14 L09aの固定点の部分。
零次数の余分な添字であるという有限な分類を、同じ境界項の定義へ戻す。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory
open scoped Simplicial

/-- L09aの証明分割：対合候補の固定点では、指定された実際の境界項が零。 -/
lemma boundaryBalancePerm_fixed_zero (A : Type u) [CommRing A] (S : SSet.{0})
    {r d : ℕ} (w : Surjection.BasisWord (r + 1) d) (q : ℕ)
    (i : BoundaryBalanceIndex w q) (hi : boundaryBalancePerm w q i = i) (x : S _⦋q⦌) :
    boundaryBalanceTerm A S w q i x = 0 := by
  have hf := (boundaryBalancePerm_fixed_iff w q i).mp hi
  have hz := (universalBoundaryPartner_fixed_iff (r + d) q
    ((boundaryBalanceIndexEquiv w q) i)).mp hf
  rcases i with oi | (ci | vi)
  · rcases oi with ⟨s, a, j⟩
    change r + d = 0 ∧ q = 0 at hz
    have hr : r = 0 := by omega
    have hd : d = 0 := by omega
    obtain ⟨_, hq⟩ := hz
    subst r
    subst d
    subst q
    have hc := (colorPositions s (positiveWord w).val a).card_le_univ
    simp only [Fintype.card_fin] at hc
    have hdeg : outputDegree s (positiveWord w) a = 0 := by
      unfold outputDegree
      omega
    simp [boundaryBalanceTerm, outputBoundaryTerm, hdeg]
  · change r + d = 0 at hz
    have hd : d = 0 := by omega
    subst d
    simp only [boundaryBalanceTerm, coefficientBoundaryTerm]
  · change q = 0 at hz
    subst q
    simp only [boundaryBalanceTerm, simplexBoundaryTerm]

end SerrePositivity.EInfinity.SimplexCuts
