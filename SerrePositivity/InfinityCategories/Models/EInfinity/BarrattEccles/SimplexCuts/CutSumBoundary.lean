module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.CutSumBoundaryInputs
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.OutputBoundarySums

/-!
模型。文献の定義との比較は後で
# 同じ一般のBF切断和の微分

Berger–Fresse §1.2.3・§2.2.7、M14 L09。
全境界項の相殺を、元の線形削除微分と元の正規化鎖微分の像へ戻す。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
open _root_.CategoryTheory _root_.SerrePositivity.TensorPowers
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A]

/-- L09：同じ切断和は、零次数も含めて元の二つの微分のLeibniz則を満たす。 -/
theorem cutSum_boundary (S : SSet.{0}) {r d q : ℕ}
    (w : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (r + 1) d) (x : S _⦋q⦌) :
    (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) (r + 1)).d (-((d + q : ℕ) : ℤ))
        (-((d + q : ℕ) : ℤ) + 1) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutSum A S w x) =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutSumCoefficientBoundary A S r d q w x +
        (-1 : ℤ) ^ d • _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutSumSimplexBoundary A S w q x := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutSum_d_eq_neg_boundarySums, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.sum_coefficientBoundaryTerm_eq, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.sum_simplexBoundaryTerm_eq]
  simp only [neg_smul]
  abel

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
