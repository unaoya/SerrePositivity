module

public import SerrePositivity.BhattScholze.RelativeFreeFrobeniusTopLinear
public import SerrePositivity.BhattScholze.DeltaWittGhostCoefficients

/-! # 自由初期変数のWitt係数と最高δ変数の全段再帰式

正確なFrobenius線形表示を全ghost等式へ代入する。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- 相対自由δ環の初期変数に対して構成したWitt係数多項式。 -/
def relativeFreeWittGhostCoefficient (D : DeltaStructure p A) (s : σ) (n : ℕ) :
    RelativeFreeDeltaRing (R := A) σ :=
  (deltaWittGhostVector (relativeFreeDeltaStructure σ D) (MvPolynomial.X (s, 0))).coeff n

/-- 第0Witt係数は初期δ変数そのもの。 -/
@[simp] theorem relativeFreeWittGhostCoefficient_zero (D : DeltaStructure p A) (s : σ) :
    relativeFreeWittGhostCoefficient D s 0 = MvPolynomial.X (s, 0) := rfl

/-- 全深さで、Witt係数から最高δ変数を引いた差のp冪倍は下位係数だけの式。 -/
theorem relativeFreeWittGhostCoefficient_top_recurrence
    (D : DeltaStructure p A) (s : σ) (n : ℕ) :
    (p : RelativeFreeDeltaRing (R := A) σ) ^ (n + 1) *
      (relativeFreeWittGhostCoefficient D s (n + 1) - MvPolynomial.X (s, n + 1)) =
        relativeFreeFiniteInitialPolynomialMap (n + 1) σ A
          (relativeFreeFrobeniusLowerPolynomial D s n) -
            ∑ i ∈ Finset.range (n + 1), (p : RelativeFreeDeltaRing (R := A) σ) ^ i *
              relativeFreeWittGhostCoefficient D s i ^ (p ^ (n + 1 - i)) := by
  have hghost := deltaWittGhostCoefficients_ghost (relativeFreeDeltaStructure σ D)
    (MvPolynomial.X (s, 0)) (n + 1)
  have hcoeff (i : ℕ) : deltaWittGhostCoefficients (relativeFreeDeltaStructure σ D)
      (MvPolynomial.X (s, 0)) i = relativeFreeWittGhostCoefficient D s i := rfl
  rw [relativeFreeFrobenius_iterate_top_linear] at hghost
  simp only [hcoeff] at hghost
  rw [Finset.sum_range_succ] at hghost
  simp only [Nat.sub_self, pow_zero, pow_one] at hghost
  linear_combination -hghost

end SerrePositivity.BhattScholze
