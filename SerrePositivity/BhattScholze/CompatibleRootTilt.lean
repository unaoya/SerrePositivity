module

public import SerrePositivity.BhattScholze.CompatibleRootPerfectQuotient
public import SerrePositivity.CommutativeAlgebra.PerfectoidUntiltNaturality

/-! # B4-3：両立する根列のtiltへの移送

根列そのものをmod pの逆極限へ送り、untiltの標準図式を証明する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R]
variable [Fact (¬ IsUnit (p : R))]

/-- 根列のn以降をmod pへ送った具体的なtilt元。 -/
def compatibleRootTilt (ρ : ℕ → R) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n) (n : ℕ) :
    PreTilt R p :=
  ⟨fun m ↦ Ideal.Quotient.mk (Ideal.span {(p : R)}) (ρ (n + m)), by
    intro m
    rw [← map_pow, ← Nat.add_assoc, hρ]⟩

/-- tilt元の全座標は元の根列のmod p像。 -/
@[simp] theorem compatibleRootTilt_coeff
    (ρ : ℕ → R) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n) (n m : ℕ) :
    PreTilt.coeff m (compatibleRootTilt ρ hρ n) =
      Ideal.Quotient.mk (Ideal.span {(p : R)}) (ρ (n + m)) := rfl

/-- tilt内でも根列は両立する。 -/
theorem compatibleRootTilt_pow
    (ρ : ℕ → R) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n) (n : ℕ) :
    compatibleRootTilt ρ hρ (n + 1) ^ p = compatibleRootTilt ρ hρ n := by
  apply Perfection.ext
  intro m
  change (Ideal.Quotient.mk _ (ρ (n + 1 + m))) ^ p = Ideal.Quotient.mk _ (ρ (n + m))
  rw [← map_pow, show n + 1 + m = n + m + 1 by omega, hρ]

/-- 根列をtiltへ送りuntiltすると、元の根列を復元する。 -/
@[simp] theorem compatibleRootTilt_untilt
    [IsAdicComplete (Ideal.span {(p : R)}) R]
    (ρ : ℕ → R) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n) (n : ℕ) :
    (compatibleRootTilt ρ hρ n).untilt = ρ n := by
  apply Perfection.teichmullerFun_spec
  intro m
  refine ⟨ρ (n + m), rfl, ?_⟩
  rw [compatibleRoots_pow p ρ hρ n m]

/-- 根をすべて消す射は、tilt上の根イデアルも消す。 -/
theorem compatibleRootTiltIdeal_le_ker
    {T : Type u} [CommRing T] [Fact (¬ IsUnit (p : T))]
    (ρ : ℕ → R) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n)
    (f : R →+* T) (hf : ∀ n, f (ρ n) = 0) :
    compatibleRootIdeal (compatibleRootTilt ρ hρ) ≤
      RingHom.ker (Perfection.map p (modPMap p f)) := by
  apply Ideal.span_le.mpr
  rintro _ ⟨n, rfl⟩
  apply Perfection.ext
  intro m
  change modPMap p f (Ideal.Quotient.mk _ (ρ (n + m))) = 0
  change Ideal.Quotient.mk _ (f (ρ (n + m))) = 0
  rw [hf, map_zero]

/-- tilt側の根イデアル商は完全。零環の商も含める。 -/
theorem compatibleRootTiltQuotient_perfectRing
    (ρ : ℕ → R) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n) :
    PerfectRing (PreTilt R p ⧸ compatibleRootIdeal (compatibleRootTilt ρ hρ)) p :=
  compatibleRootQuotient_perfectRing _ (compatibleRootTilt_pow ρ hρ)

end SerrePositivity.BhattScholze
