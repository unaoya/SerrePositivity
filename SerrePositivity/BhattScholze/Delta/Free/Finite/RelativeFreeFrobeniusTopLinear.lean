module

public import SerrePositivity.BhattScholze.Delta.Free.Finite.RelativeFreeFiniteDeltaStepIdentities
public import Mathlib.Logic.Function.Iterate

/-! # 自由初期変数のFrobenius反復の正確な最高線形項

下位部分は有限Frobenius計算で再帰的に構成する。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

/-- φ^(n+1)(X₀)から最高線形項を除いた、第n段までの具体的な多項式。 -/
def relativeFreeFrobeniusLowerPolynomial (D : DeltaStructure p A) (s : σ) :
    (n : ℕ) → MvPolynomial (σ × Fin (n + 1)) A
  | 0 => MvPolynomial.X (s, 0) ^ p
  | n + 1 => (p : MvPolynomial (σ × Fin (n + 2)) A) ^ (n + 1) *
      MvPolynomial.X (s, Fin.last (n + 1)) ^ p +
        relativeFreeFiniteFrobeniusStep n σ D (relativeFreeFrobeniusLowerPolynomial D s n)

/-- 最初の下位多項式は初期変数のp乗。 -/
@[simp] theorem relativeFreeFrobeniusLowerPolynomial_zero (D : DeltaStructure p A) (s : σ) :
    relativeFreeFrobeniusLowerPolynomial D s 0 = MvPolynomial.X (s, 0) ^ p := rfl

/-- 次の下位多項式は最高変数のp乗と、前の下位部分の有限Frobenius像。 -/
@[simp] theorem relativeFreeFrobeniusLowerPolynomial_succ
    (D : DeltaStructure p A) (s : σ) (n : ℕ) :
    relativeFreeFrobeniusLowerPolynomial D s (n + 1) =
      (p : MvPolynomial (σ × Fin (n + 2)) A) ^ (n + 1) *
        MvPolynomial.X (s, Fin.last (n + 1)) ^ p +
          relativeFreeFiniteFrobeniusStep n σ D (relativeFreeFrobeniusLowerPolynomial D s n) := rfl

/-- 全深さの自由Frobenius反復の最高変数は、p^(n+1)係数で正確に線形に現れる。 -/
theorem relativeFreeFrobenius_iterate_top_linear (D : DeltaStructure p A) (s : σ) (n : ℕ) :
    (relativeFreeDeltaStructure σ D).frobeniusLift^[n + 1] (MvPolynomial.X (s, 0)) =
      (p : RelativeFreeDeltaRing (R := A) σ) ^ (n + 1) * MvPolynomial.X (s, n + 1) +
        relativeFreeFiniteInitialPolynomialMap (n + 1) σ A
          (relativeFreeFrobeniusLowerPolynomial D s n) := by
  induction n with
  | zero =>
      rw [Function.iterate_one, DeltaStructure.frobeniusLift_apply,
        relativeFreeDeltaStructure_delta_X]
      simp [relativeFreeFrobeniusLowerPolynomial, relativeFreeFiniteInitialPolynomialMap,
        add_comm]
  | succ n ih =>
      rw [Function.iterate_succ_apply' _ (n + 1), ih, map_add, map_mul, map_pow, map_natCast,
        DeltaStructure.frobeniusLift_apply, relativeFreeDeltaStructure_delta_X,
        ← relativeFreeFiniteFrobeniusStep_image n σ D,
        relativeFreeFrobeniusLowerPolynomial_succ, map_add, map_mul, map_pow, map_natCast]
      simp only [relativeFreeFiniteInitialPolynomialMap, MvPolynomial.rename_X,
        Fin.val_last, map_pow]
      rw [pow_succ]
      ring

/-- 自由初期変数のφ^n像を初期n+1段に置く、具体的な有限多項式。 -/
def relativeFreeFrobeniusFinitePolynomial (D : DeltaStructure p A) (s : σ) :
    (n : ℕ) → MvPolynomial (σ × Fin (n + 1)) A
  | 0 => MvPolynomial.X (s, 0)
  | n + 1 => (p : MvPolynomial (σ × Fin (n + 2)) A) ^ (n + 1) *
      MvPolynomial.X (s, Fin.last (n + 1)) +
        relativeFreeFiniteStepInclusion n σ (relativeFreeFrobeniusLowerPolynomial D s n)

/-- 有限Frobenius多項式の包含像は、実際のφ反復の像。 -/
theorem relativeFreeFrobeniusFinitePolynomial_image (D : DeltaStructure p A) (s : σ) (n : ℕ) :
    relativeFreeFiniteInitialPolynomialMap (n + 1) σ A
      (relativeFreeFrobeniusFinitePolynomial D s n) =
        (relativeFreeDeltaStructure σ D).frobeniusLift^[n] (MvPolynomial.X (s, 0)) := by
  cases n with
  | zero => simp [relativeFreeFrobeniusFinitePolynomial, relativeFreeFiniteInitialPolynomialMap]
  | succ n =>
      rw [relativeFreeFrobenius_iterate_top_linear]
      simp only [relativeFreeFrobeniusFinitePolynomial, map_add, map_mul, map_pow, map_natCast]
      have hx : relativeFreeFiniteInitialPolynomialMap (n + 2) σ A
          (MvPolynomial.X (s, Fin.last (n + 1))) = MvPolynomial.X (s, n + 1) := by
        simp [relativeFreeFiniteInitialPolynomialMap]
      rw [hx]
      congr 1
      exact RingHom.congr_fun (relativeFreeFiniteStepInclusion_comp_initial (A := A) n σ) _

/-- 自由初期変数のφ^n像には第n段以下の変数しか現れない。 -/
theorem relativeFreeFrobenius_iterate_variable_bound (D : DeltaStructure p A) (s : σ) (n : ℕ)
    (z : σ × ℕ)
    (hz : z ∈ ((relativeFreeDeltaStructure σ D).frobeniusLift^[n]
      (MvPolynomial.X (s, 0))).vars) : z.2 ≤ n := by
  rw [← relativeFreeFrobeniusFinitePolynomial_image D s n] at hz
  change z ∈ (MvPolynomial.rename (fun x : σ × Fin (n + 1) => (x.1, x.2.val))
    (relativeFreeFrobeniusFinitePolynomial D s n)).vars at hz
  obtain ⟨⟨t, i⟩, _, he⟩ := MvPolynomial.mem_vars_rename _ _ hz
  have hn := i.isLt
  have hval := congrArg Prod.snd he
  change i.val = z.2 at hval
  omega

end SerrePositivity.BhattScholze
