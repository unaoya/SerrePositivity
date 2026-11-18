module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.BoundaryPairingValues

/-!
模型。文献の定義との比較は後で
# BF全境界項の有限和の相殺

Berger–Fresse §2.2.7、M14 L09の証明分割。
同じ対合と固定点の零を既存の有限和の相殺則に適用する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
open _root_.CategoryTheory _root_.SerrePositivity.TensorPowers
open scoped _root_.Simplicial

/-- C256：同じ実境界値の全有限和は、元の加群で零となる。 -/
lemma sum_boundaryBalanceTerm_eq_zero (A : Type u) [CommRing A] (S : SSet.{0}) {r d : ℕ}
    (w : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (r + 1) d) (q : ℕ) (x : S _⦋q⦌) :
    ∑ i : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.BoundaryBalanceIndex w q, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryBalanceTerm A S w q i x = 0 := by
  classical
  apply Finset.sum_ninvolution (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryBalancePerm w q)
  · intro i
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryBalancePerm_neg A S w q x i]
    exact add_neg_cancel _
  · intro i hne he
    exact hne (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryBalancePerm_fixed_zero A S w q i he x)
  · intro i
    exact Finset.mem_univ _
  · exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryBalancePerm_involutive w q

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
