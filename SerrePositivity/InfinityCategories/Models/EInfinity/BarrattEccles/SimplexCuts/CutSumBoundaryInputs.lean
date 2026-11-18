module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.CoefficientDifferentialSums
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.InputBoundarySums
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.Normalization
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.GeneratorBoundary

/-!
模型。文献の定義との比較は後で
# 同じ線形切断作用による係数境界と入力境界の像

Berger–Fresse §1.2.3・§2.2.7、M14 L09の証明分割。
既存のrawComponentとnormalizedComponentへ、元の二つの微分を適用した値の記法。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
open _root_.CategoryTheory _root_.SerrePositivity.TensorPowers
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A]

/-- 同じ線形切断作用による、元の係数の線形削除微分の像。次数零では零。 -/
def cutSumCoefficientBoundary (S : SSet.{0}) (r : ℕ) : (d q : ℕ) →
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (r + 1) d → S _⦋q⦌ →
      (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) (r + 1)).X (-((d + q : ℕ) : ℤ) + 1)
  | 0, _, _, _ => 0
  | d + 1, q, w, x => by
    have h : -((d + q : ℕ) : ℤ) = -(((d + 1) + q : ℕ) : ℤ) + 1 := by omega
    exact (eqToHom (congrArg (fun z : ℤ => (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) (r + 1)).X z) h)).hom
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.rawComponent A S r d q
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.differential A (r + 1) d
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A (r + 1) (d + 1) (ULift.up w)))
        (ModuleCat.freeMk (ULift.up x)))

/-- 同じ線形切断作用による、元の正規化鎖微分の像。入力次数零では零。 -/
def cutSumSimplexBoundary (S : SSet.{0}) {r d : ℕ} (w : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (r + 1) d) :
    (q : ℕ) → S _⦋q⦌ → (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) (r + 1)).X (-((d + q : ℕ) : ℤ) + 1)
  | 0, _ => 0
  | q + 1, x => by
    have h : -((d + q : ℕ) : ℤ) = -((d + (q + 1) : ℕ) : ℤ) + 1 := by omega
    exact (eqToHom (congrArg (fun z : ℤ => (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) (r + 1)).X z) h)).hom
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.normalizedComponent A S r d q (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A (r + 1) d (ULift.up w))
        ((_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A S).d (q + 1) q (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator A S (q + 1) x)))

/-- C300：全係数境界和は、元の線形係数微分の像の負号。 -/
lemma sum_coefficientBoundaryTerm_eq (S : SSet.{0}) {r d : ℕ}
    (w : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (r + 1) d) (q : ℕ) (x : S _⦋q⦌) :
    (∑ c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.CoefficientBoundaryIndex r d q, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.coefficientBoundaryTerm A S r d q w c x) =
      -_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutSumCoefficientBoundary A S r d q w x := by
  cases d with
  | zero => simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.sum_coefficientBoundaryTerm_zero, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutSumCoefficientBoundary, neg_zero]
  | succ d => exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.sum_coefficientBoundaryTerm_succ A S w x (by omega)

/-- C301：同じ正規化鎖微分の像は、同じcutSumの交代面和。 -/
lemma cutSumSimplexBoundary_succ_eq_sum (S : SSet.{0}) {r d q : ℕ}
    (w : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (r + 1) d) (x : S _⦋q + 1⦌)
    (h : -((d + q : ℕ) : ℤ) = -((d + (q + 1) : ℕ) : ℤ) + 1) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutSumSimplexBoundary A S w (q + 1) x =
      ∑ i : Fin (q + 2), (-1 : ℤ) ^ i.val •
        (eqToHom (congrArg (fun z : ℤ => (power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) (r + 1)).X z) h)).hom
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutSum A S w (S.δ i x)) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutSumSimplexBoundary, _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.generator_d, map_sum, map_zsmul,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.normalizedComponent_gen, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.rawComponent_value]

/-- C302：全入力境界和は、元の正規化鎖微分の像と元のKoszul符号。 -/
lemma sum_simplexBoundaryTerm_eq (S : SSet.{0}) {r d : ℕ}
    (w : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord (r + 1) d) (q : ℕ) (x : S _⦋q⦌) :
    (∑ c : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.SimplexBoundaryIndex r d q, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.simplexBoundaryTerm A S w q c x) =
      -((-1 : ℤ) ^ d) • _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutSumSimplexBoundary A S w q x := by
  cases q with
  | zero => simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.sum_simplexBoundaryTerm_zero, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutSumSimplexBoundary, smul_zero]
  | succ q =>
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cutSumSimplexBoundary_succ_eq_sum A S w x (by omega)]
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.sum_simplexBoundaryTerm_succ A S w x (by omega)

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
