module

public import SerrePositivity.BhattScholze.RelativeFreeFiniteDeltaAdicEstimate
public import Mathlib.Logic.Function.Iterate

/-! # 有限δ計算の全反復と誤差冪の損失

初期段を一段ずつ増やし、相対自由δ環の実際の反復と比較する。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (N : ℕ) (σ : Type v)

/-- 初期有限多項式に有限δ計算をk回適用した、具体的な次段多項式。 -/
def relativeFreeFiniteDeltaIterate (D : DeltaStructure p A)
    (f : MvPolynomial (σ × Fin (N + 1)) A) :
    (k : ℕ) → MvPolynomial (σ × Fin (N + k + 1)) A
  | 0 => f
  | k + 1 => relativeFreeFiniteDeltaStep (N + k) σ D (relativeFreeFiniteDeltaIterate D f k)

/-- 零回反復は初期有限多項式。 -/
@[simp] theorem relativeFreeFiniteDeltaIterate_zero (D : DeltaStructure p A)
    (f : MvPolynomial (σ × Fin (N + 1)) A) :
    relativeFreeFiniteDeltaIterate N σ D f 0 = f := rfl

/-- 次の反復は一段大きい有限環でのδ計算。 -/
@[simp] theorem relativeFreeFiniteDeltaIterate_succ (D : DeltaStructure p A)
    (f : MvPolynomial (σ × Fin (N + 1)) A) (k : ℕ) :
    relativeFreeFiniteDeltaIterate N σ D f (k + 1) =
      relativeFreeFiniteDeltaStep (N + k) σ D (relativeFreeFiniteDeltaIterate N σ D f k) := rfl

/-- 全反復有限多項式の標準包含像は、実際の相対自由δ環のδ反復。 -/
theorem relativeFreeFiniteDeltaIterate_image (D : DeltaStructure p A)
    (f : MvPolynomial (σ × Fin (N + 1)) A) (k : ℕ) :
    relativeFreeFiniteInitialPolynomialMap (N + k + 1) σ A
      (relativeFreeFiniteDeltaIterate N σ D f k) =
        (relativeFreeDeltaStructure σ D).delta^[k]
          (relativeFreeFiniteInitialPolynomialMap (N + 1) σ A f) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [relativeFreeFiniteDeltaIterate_succ]
      change relativeFreeFiniteInitialPolynomialMap (N + k + 2) σ A
        (relativeFreeFiniteDeltaStep (N + k) σ D (relativeFreeFiniteDeltaIterate N σ D f k)) = _
      rw [← relativeFreeFiniteDeltaStep_delta_image (N + k) σ D, ih]
      exact (Function.iterate_succ_apply' (relativeFreeDeltaStructure σ D).delta k _).symm

/-- 初期誤差がJ^(m+k)なら、k回の有限δ計算後の包含像の誤差はJ^m。
有限商のδ構造を要求せず、実際の相対自由δ環の冪評価を反復する。 -/
theorem relativeFreeFiniteDeltaIterate_sub_image_mem_pow (D : DeltaStructure p A)
    (J : Ideal (RelativeFreeDeltaRing (R := A) σ))
    (hp : (p : RelativeFreeDeltaRing (R := A) σ) ∈ J)
    (m k : ℕ) (f g : MvPolynomial (σ × Fin (N + 1)) A)
    (hfg : relativeFreeFiniteInitialPolynomialMap (N + 1) σ A f -
      relativeFreeFiniteInitialPolynomialMap (N + 1) σ A g ∈ J ^ (m + k)) :
    relativeFreeFiniteInitialPolynomialMap (N + k + 1) σ A
      (relativeFreeFiniteDeltaIterate N σ D f k) -
        relativeFreeFiniteInitialPolynomialMap (N + k + 1) σ A
          (relativeFreeFiniteDeltaIterate N σ D g k) ∈ J ^ m := by
  rw [relativeFreeFiniteDeltaIterate_image, relativeFreeFiniteDeltaIterate_image]
  induction k generalizing m with
  | zero => exact hfg
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      apply (relativeFreeDeltaStructure σ D).delta_sub_mem_pow J hp m
      apply ih (m + 1)
      simpa only [Nat.add_assoc, Nat.add_comm 1 k] using hfg

end SerrePositivity.BhattScholze
