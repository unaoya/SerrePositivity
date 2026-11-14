module

public import SerrePositivity.EInfinity.SimplexCuts.CoefficientDifferentialSums
public import SerrePositivity.EInfinity.SimplexCuts.InputBoundarySums
public import SerrePositivity.EInfinity.SimplexCuts.Normalization
public import SerrePositivity.EInfinity.SimplexCuts.GeneratorBoundary

/-!
# 同じ線形切断作用による係数境界と入力境界の像

Berger–Fresse §1.2.3・§2.2.7、M14 L09の証明分割。
既存のrawComponentとnormalizedComponentへ、元の二つの微分を適用した値の記法。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory SerrePositivity.TensorPowers
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- 同じ線形切断作用による、元の係数の線形削除微分の像。次数零では零。 -/
def cutSumCoefficientBoundary (S : SSet.{0}) (r : ℕ) : (d q : ℕ) →
    Surjection.BasisWord (r + 1) d → S _⦋q⦌ →
      (power (chains A S) (r + 1)).X (-((d + q : ℕ) : ℤ) + 1)
  | 0, _, _, _ => 0
  | d + 1, q, w, x => by
    have h : -((d + q : ℕ) : ℤ) = -(((d + 1) + q : ℕ) : ℤ) + 1 := by omega
    exact (eqToHom (congrArg (fun z : ℤ => (power (chains A S) (r + 1)).X z) h)).hom
      (rawComponent A S r d q
        (Surjection.differential A (r + 1) d
          (Surjection.basis A (r + 1) (d + 1) (ULift.up w)))
        (ModuleCat.freeMk (ULift.up x)))

/-- 同じ線形切断作用による、元の正規化鎖微分の像。入力次数零では零。 -/
def cutSumSimplexBoundary (S : SSet.{0}) {r d : ℕ} (w : Surjection.BasisWord (r + 1) d) :
    (q : ℕ) → S _⦋q⦌ → (power (chains A S) (r + 1)).X (-((d + q : ℕ) : ℤ) + 1)
  | 0, _ => 0
  | q + 1, x => by
    have h : -((d + q : ℕ) : ℤ) = -((d + (q + 1) : ℕ) : ℤ) + 1 := by omega
    exact (eqToHom (congrArg (fun z : ℤ => (power (chains A S) (r + 1)).X z) h)).hom
      (normalizedComponent A S r d q (Surjection.basis A (r + 1) d (ULift.up w))
        ((AlexanderWhitney.chains A S).d (q + 1) q (AlexanderWhitney.generator A S (q + 1) x)))

/-- C300：全係数境界和は、元の線形係数微分の像の負号。 -/
lemma sum_coefficientBoundaryTerm_eq (S : SSet.{0}) {r d : ℕ}
    (w : Surjection.BasisWord (r + 1) d) (q : ℕ) (x : S _⦋q⦌) :
    (∑ c : CoefficientBoundaryIndex r d q, coefficientBoundaryTerm A S r d q w c x) =
      -cutSumCoefficientBoundary A S r d q w x := by
  cases d with
  | zero => simp only [sum_coefficientBoundaryTerm_zero, cutSumCoefficientBoundary, neg_zero]
  | succ d => exact sum_coefficientBoundaryTerm_succ A S w x (by omega)

/-- C301：同じ正規化鎖微分の像は、同じcutSumの交代面和。 -/
lemma cutSumSimplexBoundary_succ_eq_sum (S : SSet.{0}) {r d q : ℕ}
    (w : Surjection.BasisWord (r + 1) d) (x : S _⦋q + 1⦌)
    (h : -((d + q : ℕ) : ℤ) = -((d + (q + 1) : ℕ) : ℤ) + 1) :
    cutSumSimplexBoundary A S w (q + 1) x =
      ∑ i : Fin (q + 2), (-1 : ℤ) ^ i.val •
        (eqToHom (congrArg (fun z : ℤ => (power (chains A S) (r + 1)).X z) h)).hom
          (cutSum A S w (S.δ i x)) := by
  simp only [cutSumSimplexBoundary, AlexanderWhitney.generator_d, map_sum, map_zsmul,
    normalizedComponent_gen, rawComponent_value]

/-- C302：全入力境界和は、元の正規化鎖微分の像と元のKoszul符号。 -/
lemma sum_simplexBoundaryTerm_eq (S : SSet.{0}) {r d : ℕ}
    (w : Surjection.BasisWord (r + 1) d) (q : ℕ) (x : S _⦋q⦌) :
    (∑ c : SimplexBoundaryIndex r d q, simplexBoundaryTerm A S w q c x) =
      -((-1 : ℤ) ^ d) • cutSumSimplexBoundary A S w q x := by
  cases q with
  | zero => simp only [sum_simplexBoundaryTerm_zero, cutSumSimplexBoundary, smul_zero]
  | succ q =>
    rw [cutSumSimplexBoundary_succ_eq_sum A S w x (by omega)]
    exact sum_simplexBoundaryTerm_succ A S w x (by omega)

end SerrePositivity.EInfinity.SimplexCuts
