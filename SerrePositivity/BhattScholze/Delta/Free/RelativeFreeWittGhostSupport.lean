module

public import SerrePositivity.BhattScholze.Delta.Free.RelativeFreeWittGhostRecurrence
public import Mathlib.Algebra.MvPolynomial.Supported

/-! # 全Witt係数と最高δ変数の差の下位変数所属

p乗算単射だけで係数の零判定を戻し、全段再帰式を強帰納する。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}

omit [Fact p.Prime] in
private theorem prime_pow_mul_injective
    (hp : Function.Injective (fun a : A => (p : A) * a)) (n : ℕ) :
    Function.Injective (fun a : A => (p : A) ^ n * a) := by
  induction n with
  | zero =>
      intro a b h
      simpa only [pow_zero, one_mul] using h
  | succ n ih =>
      intro a b h
      apply ih
      apply hp
      simpa only [pow_succ', mul_assoc] using h

private theorem vars_C_mul_regular {τ : Type*} (c : A)
    (hc : Function.Injective (fun a : A => c * a)) (f : MvPolynomial τ A) :
    (MvPolynomial.C c * f).vars = f.vars := by
  classical
  have hz (a : A) : c * a = 0 ↔ a = 0 :=
    ⟨fun h => hc (h.trans (mul_zero c).symm), fun h => by rw [h, mul_zero]⟩
  ext z
  simp only [MvPolynomial.mem_vars_iff_mem_support, MvPolynomial.mem_support_iff,
    MvPolynomial.coeff_C_mul, ne_eq, hz]

omit [Fact p.Prime] in
private theorem mem_supported_of_prime_pow_mul
    (hp : Function.Injective (fun a : A => (p : A) * a)) (n : ℕ)
    (f : RelativeFreeDeltaRing (R := A) σ) (s : Set (σ × ℕ))
    (hf : (p : RelativeFreeDeltaRing (R := A) σ) ^ n * f ∈ MvPolynomial.supported A s) :
    f ∈ MvPolynomial.supported A s := by
  have he : (p : RelativeFreeDeltaRing (R := A) σ) ^ n = MvPolynomial.C ((p : A) ^ n) := by
    rw [map_pow, map_natCast]
  have hv : ((p : RelativeFreeDeltaRing (R := A) σ) ^ n * f).vars = f.vars := by
    rw [he]
    exact vars_C_mul_regular _ (prime_pow_mul_injective hp n) f
  apply MvPolynomial.mem_supported.mpr
  rw [← hv]
  exact MvPolynomial.mem_supported.mp hf

/-- p乗算単射の下で、全Witt係数と最高δ変数の差は下位変数だけの多項式。 -/
theorem relativeFreeWittGhostCoefficient_sub_X_mem_supported (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a)) (s : σ) (n : ℕ) :
    relativeFreeWittGhostCoefficient D s n - MvPolynomial.X (s, n) ∈
      MvPolynomial.supported A {z : σ × ℕ | z.2 < n} := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          simp only [relativeFreeWittGhostCoefficient_zero, sub_self]
          exact Subalgebra.zero_mem _
      | succ n =>
          let S := MvPolynomial.supported A {z : σ × ℕ | z.2 < n + 1}
          have hX (i : ℕ) (hi : i < n + 1) :
              (MvPolynomial.X (s, i) : RelativeFreeDeltaRing (R := A) σ) ∈ S := by
            apply Algebra.subset_adjoin
            exact ⟨(s, i), hi, rfl⟩
          have hcoef (i : ℕ) (hi : i < n + 1) : relativeFreeWittGhostCoefficient D s i ∈ S := by
            have hlow := (MvPolynomial.supported_mono (R := A)
              (fun z hz => Nat.lt_trans hz hi)) (ih i hi)
            have he := S.add_mem hlow (hX i hi)
            simpa only [sub_add_cancel] using he
          have hlower : relativeFreeFiniteInitialPolynomialMap (n + 1) σ A
              (relativeFreeFrobeniusLowerPolynomial D s n) ∈ S := by
            apply MvPolynomial.mem_supported.mpr
            intro z hz
            change z ∈ (MvPolynomial.rename (fun x : σ × Fin (n + 1) => (x.1, x.2.val))
              (relativeFreeFrobeniusLowerPolynomial D s n)).vars at hz
            obtain ⟨⟨t, i⟩, _, he⟩ := MvPolynomial.mem_vars_rename _ _ hz
            have hi := i.isLt
            have hval := congrArg Prod.snd he
            change i.val = z.2 at hval
            change z.2 < n + 1
            omega
          have hsum : (∑ i ∈ Finset.range (n + 1), (p : RelativeFreeDeltaRing (R := A) σ) ^ i *
              relativeFreeWittGhostCoefficient D s i ^ (p ^ (n + 1 - i))) ∈ S := by
            apply S.sum_mem
            intro i hi
            exact S.mul_mem (S.pow_mem (S.natCast_mem p) i)
              (S.pow_mem (hcoef i (Finset.mem_range.mp hi)) _)
          apply mem_supported_of_prime_pow_mul hp (n + 1)
          rw [relativeFreeWittGhostCoefficient_top_recurrence]
          exact S.sub_mem hlower hsum

/-- 各Witt係数の変数は第n段以下。整域性・G4は不要。 -/
theorem relativeFreeWittGhostCoefficient_variable_bound (D : DeltaStructure p A)
    (hp : Function.Injective (fun a : A => (p : A) * a)) (s : σ) (n : ℕ)
    (z : σ × ℕ) (hz : z ∈ (relativeFreeWittGhostCoefficient D s n).vars) : z.2 ≤ n := by
  classical
  have hlow := relativeFreeWittGhostCoefficient_sub_X_mem_supported D hp s n
  have hX : (MvPolynomial.X (s, n) : RelativeFreeDeltaRing (R := A) σ) ∈
      MvPolynomial.supported A {z : σ × ℕ | z.2 ≤ n} := by
    apply Algebra.subset_adjoin
    exact ⟨(s, n), (by change n ≤ n; exact le_rfl), rfl⟩
  have hlow' := (MvPolynomial.supported_mono (R := A) (fun z hz => Nat.le_of_lt hz)) hlow
  have he := (MvPolynomial.supported A {z : σ × ℕ | z.2 ≤ n}).add_mem hlow' hX
  rw [sub_add_cancel] at he
  exact MvPolynomial.mem_supported.mp he hz

end SerrePositivity.BhattScholze
