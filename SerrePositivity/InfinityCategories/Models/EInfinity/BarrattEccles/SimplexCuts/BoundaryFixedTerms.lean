module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.BoundaryPartnerFixedPoints
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.BoundaryTerms

/-!
模型。文献の定義との比較は後で
# 全境界の対合の固定点での零

Berger–Fresse §2.2.7、M14 L09aの固定点の部分。
零次数の余分な添字であるという有限な分類を、同じ境界項の定義へ戻す。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
open _root_.CategoryTheory
open scoped _root_.Simplicial

/-- L09aの証明分割：対合候補の固定点では、指定された実際の境界項が零。 -/
lemma boundaryBalancePerm_fixed_zero (A : Type u) [CommRing A] (S : SSet.{0})
    {r d : ℕ} (w : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (r + 1) d) (q : ℕ)
    (i : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.BoundaryBalanceIndex w q) (hi : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryBalancePerm w q i = i) (x : S _⦋q⦌) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryBalanceTerm A S w q i x = 0 := by
  have hf := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryBalancePerm_fixed_iff w q i).mp hi
  have hz := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.universalBoundaryPartner_fixed_iff (r + d) q
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryBalanceIndexEquiv w q) i)).mp hf
  rcases i with oi | (ci | vi)
  · rcases oi with ⟨s, a, j⟩
    change r + d = 0 ∧ q = 0 at hz
    have hr : r = 0 := by omega
    have hd : d = 0 := by omega
    obtain ⟨_, hq⟩ := hz
    subst r
    subst d
    subst q
    have hc := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.colorPositions s (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord w).val a).card_le_univ
    simp only [Fintype.card_fin] at hc
    have hdeg : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord w) a = 0 := by
      unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree
      omega
    simp [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryBalanceTerm, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputBoundaryTerm, hdeg]
  · change r + d = 0 at hz
    have hd : d = 0 := by omega
    subst d
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryBalanceTerm, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.coefficientBoundaryTerm]
  · change q = 0 at hz
    subst q
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryBalanceTerm, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.simplexBoundaryTerm]

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
