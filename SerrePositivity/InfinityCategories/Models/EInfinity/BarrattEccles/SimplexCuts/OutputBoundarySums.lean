module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.CutTermDifferential
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.BoundarySumCancellation

/-!
模型。文献の定義との比較は後で
# 同じ切断和の微分と全実境界項

Berger–Fresse §2.2.7、M14 L09の証明分割。
切断ごとの微分則と全境界項の相殺を、同じ共通次数での切断和へ戻す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
open _root_.CategoryTheory _root_.SerrePositivity.TensorPowers
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A]

/-- C258：同じ切断和の微分は、同じ指定出力境界値を移送した全和。 -/
lemma cutSum_d_eq_sum_outputBoundaryTerm (S : SSet.{0})
    {r d q : ℕ} (w : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (r + 1) d) (x : S _⦋q⦌)
    (h : -((r + d + q + 1 - (r + 1) : ℕ) : ℤ) + 1 = -((d + q : ℕ) : ℤ) + 1) :
    (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) (r + 1)).d (-((d + q : ℕ) : ℤ))
        (-((d + q : ℕ) : ℤ) + 1) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutSum A S w x) =
      ∑ s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut (r + d) q, ∑ a : Fin (r + 1),
        ∑ j : Fin (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputDegree s (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord w) a + 1),
          (eqToHom (congrArg (fun z : ℤ => (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) (r + 1)).X z) h)).hom
            (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.outputBoundaryTerm A S s (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord w) a j x) := by
  have h0 : -((r + d + q + 1 - (r + 1) : ℕ) : ℤ) = -((d + q : ℕ) : ℤ) := by omega
  have hc := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.complex_d_cast_source_target A (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) (r + 1))
    (i := -((r + d + q + 1 - (r + 1) : ℕ) : ℤ)) (i' := -((d + q : ℕ) : ℤ))
    (j := -((r + d + q + 1 - (r + 1) : ℕ) : ℤ) + 1) (j' := -((d + q : ℕ) : ℤ) + 1)
    h0 h (∑ s : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Cut (r + d) q, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutTerm A S s (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.positiveWord w) x)
  simp only [map_sum, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutTerm_d_eq_sum_outputBoundaryTerm] at hc
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutSum
  simp only [map_sum]
  convert hc using 1

/-- C282：全出力境界項の同じ有限和は、元のcutSumの微分。 -/
lemma sum_boundaryBalanceTerm_output_eq_d_cutSum (S : SSet.{0}) {r d : ℕ}
    (w : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (r + 1) d) (q : ℕ) (x : S _⦋q⦌) :
    (∑ i : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.OutputBoundaryIndex w q, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryBalanceTerm A S w q (.inl i) x) =
      (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) (r + 1)).d (-((d + q : ℕ) : ℤ))
        (-((d + q : ℕ) : ℤ) + 1) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutSum A S w x) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutSum_d_eq_sum_outputBoundaryTerm A S w x (by omega)]
  simp only [Fintype.sum_sigma, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.boundaryBalanceTerm]

/-- C283：同じcutSumの微分は、残る二つの元の実境界和の和の負号。 -/
lemma cutSum_d_eq_neg_boundarySums (S : SSet.{0}) {r d : ℕ}
    (w : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (r + 1) d) (q : ℕ) (x : S _⦋q⦌) :
    (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) (r + 1)).d (-((d + q : ℕ) : ℤ))
        (-((d + q : ℕ) : ℤ) + 1) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutSum A S w x) =
      -((∑ c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.CoefficientBoundaryIndex r d q, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.coefficientBoundaryTerm A S r d q w c x) +
        ∑ i : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.SimplexBoundaryIndex r d q, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.simplexBoundaryTerm A S w q i x) := by
  have ht := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.sum_boundaryBalanceTerm_eq_zero A S w q x
  simp only [Fintype.sum_sum_type] at ht
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.sum_boundaryBalanceTerm_output_eq_d_cutSum A S w q x] at ht
  change (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) (r + 1)).d (-((d + q : ℕ) : ℤ))
      (-((d + q : ℕ) : ℤ) + 1) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutSum A S w x) +
      ((∑ c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.CoefficientBoundaryIndex r d q, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.coefficientBoundaryTerm A S r d q w c x) +
        ∑ i : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.SimplexBoundaryIndex r d q, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.simplexBoundaryTerm A S w q i x) = 0 at ht
  exact eq_neg_of_add_eq_zero_left ht

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
