module

public import SerrePositivity.BhattScholze.Delta.DividedPower.DeltaPDivisionLocalization
public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.Division.DeltaPDivisionRawRegular

/-! # raw一元δ p除算包のA[1/p]への具体的埋め込み

既存の標準δ評価とp局所化比較を使う。実際の像部分環との同型も供給する。
分冪包との一致・完全忠実平坦性は別工程。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

section General
variable {σ : Type v} (D : DeltaStructure p A) (a : σ → A)
local notation "B₀" => DeltaAdjoinDivision D (p : A) a
local notation "Bₚ" => Localization.Away (p : B₀)

/-- raw包がp正則なら、具体的δ評価B→A[1/p]は単射。 -/
theorem deltaPDivisionToAway_injective_of_p_mul_injective
    (hp : Function.Injective (fun x : B₀ ↦ (p : B₀) * x)) :
    Function.Injective (deltaPDivisionToAway D a) := by
  have hj : Function.Injective (algebraMap B₀ Bₚ) := by
    intro x z hxz
    have hzero : algebraMap B₀ Bₚ (x - z) = 0 := by rw [map_sub, hxz, sub_self]
    obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff
      (Submonoid.powers (p : B₀)) Bₚ (x - z)).mp hzero
    obtain ⟨N, hN⟩ := (Submonoid.mem_powers_iff (m : B₀) (p : B₀)).mp m.property
    have hreg : IsLeftRegular (p : B₀) := by
      intro t w htw
      exact hp htw
    apply sub_eq_zero.mp
    apply hreg.pow N
    change (p : B₀) ^ N * (x - z) = (p : B₀) ^ N * 0
    rw [hN, hm, mul_zero]
  intro x z hxz
  apply hj
  calc
    algebraMap B₀ Bₚ x = deltaPDivisionAwayToAway D a (deltaPDivisionToAway D a x) :=
      (RingHom.congr_fun (deltaPDivisionAwayToAway_comp_toAway D a) x).symm
    _ = deltaPDivisionAwayToAway D a (deltaPDivisionToAway D a z) := congrArg _ hxz
    _ = algebraMap B₀ Bₚ z := RingHom.congr_fun (deltaPDivisionAwayToAway_comp_toAway D a) z

/-- 具体的δ評価の像部分環は局所化上のδ作用で安定。単射性は不要。 -/
theorem deltaPDivisionToAway_range_delta_stable
    (x : Localization.Away (p : A)) (hx : x ∈ (deltaPDivisionToAway D a).range) :
    (deltaPDivisionAwayStructure D).delta x ∈ (deltaPDivisionToAway D a).range := by
  obtain ⟨b, rfl⟩ := hx
  exact ⟨(deltaAdjoinDivisionStructure D (p : A) a).delta b,
    (deltaPDivisionToAway_spec D a).1 b⟩
end General

section Shift
variable {σ : Type v} (D : DeltaStructure p A) (y : σ → A) (s : σ)
local notation "a₀" => fun t ↦ D.frobeniusLift (y t)
local notation "f₀" => deltaPDivisionToAway D a₀
local notation "j₀" => deltaAdjoinDivisionMap D (p : A) a₀
local notation "v₀" => deltaAdjoinDivisionVariable D (p : A) a₀
local notation "Aₚ" => Localization.Away (p : A)

/-- φ(y)/pからδ(y)を引いた元の像は、A[1/p]内の具体的なy^p/p。 -/
theorem deltaPDivisionToAway_shifted_variable :
    f₀ (v₀ s - j₀ (D.delta (y s))) =
      IsLocalization.Away.invSelf (p : A) * (algebraMap A Aₚ (y s)) ^ p := by
  have hb : f₀ (j₀ (D.delta (y s))) = algebraMap A Aₚ (D.delta (y s)) :=
    RingHom.congr_fun (deltaPDivisionToAway_spec D a₀).2.1 _
  have hi : IsLocalization.Away.invSelf (p : A) * algebraMap A Aₚ (p : A) = 1 := by
    rw [mul_comm, IsLocalization.Away.mul_invSelf]
  rw [map_sub, (deltaPDivisionToAway_spec D a₀).2.2, hb, D.frobeniusLift_apply,
    map_add, map_pow, map_mul, mul_add, ← mul_assoc, hi, one_mul, add_sub_cancel_right]
end Shift

section Unary
variable {σ : Type u} [Unique σ] (D : DeltaStructure p A) (y : A)
variable (hpA : Function.Injective (fun x : A ↦ (p : A) * x))
variable (hg : Function.Injective (WittVector.ghostMap :
  WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
variable (v : Aˣ) (hv : (v : A) = D.delta (p : A))
variable (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
  (Ideal.Quotient.mk (Ideal.span {(p : A)}) y))
local notation "a₀" => fun _ : σ ↦ D.frobeniusLift y
local notation "B₀" => DeltaAdjoinDivision D (p : A) a₀
local notation "j₀" => deltaAdjoinDivisionMap D (p : A) a₀
local notation "f₀" => deltaPDivisionToAway D a₀
local notation "Aₚ" => Localization.Away (p : A)
include hpA hg hv hy

/-- 明示した中間入力の下で、一元rawδ包A{φ(y)/p}はA[1/p]へ単射に写る。 -/
theorem deltaPDivisionRawToAway_injective : Function.Injective f₀ :=
  deltaPDivisionToAway_injective_of_p_mul_injective D a₀
    (deltaPDivisionRaw_p_mul_injective (σ := σ) D y hpA hg v hv hy)

omit hv in
/-- 源がp進完備なら単元δ(p)の指定を省いた同じ具体的埋め込みを得る。 -/
theorem deltaPDivisionRawToAway_injective_of_adicComplete
    [IsAdicComplete (Ideal.span {(p : A)}) A] : Function.Injective f₀ :=
  deltaPDivisionToAway_injective_of_p_mul_injective D a₀
    (deltaPDivisionRaw_p_mul_injective_of_adicComplete (σ := σ) D y hpA hg hy)

/-- raw一元δ包を、A[1/p]内の具体的δ評価の像部分環と同定する。 -/
def deltaPDivisionRawRangeEquiv : B₀ ≃+* (f₀).range :=
  RingEquiv.ofBijective (f₀).rangeRestrict
    ⟨fun _ _ h ↦ deltaPDivisionRawToAway_injective (σ := σ) D y hpA hg v hv hy
      (congrArg Subtype.val h), (f₀).rangeRestrict_surjective⟩

/-- 部分環表示の値は実際のA[1/p]へのδ評価。 -/
theorem deltaPDivisionRawRangeEquiv_apply (b : B₀) :
    (deltaPDivisionRawRangeEquiv (σ := σ) D y hpA hg v hv hy b : Aₚ) = f₀ b := rfl

/-- 部分環表示は元のAからの標準射を保つ。 -/
theorem deltaPDivisionRawRangeEquiv_coeff (r : A) :
    (deltaPDivisionRawRangeEquiv (σ := σ) D y hpA hg v hv hy (j₀ r) : Aₚ) =
      algebraMap A Aₚ r := by
  rw [deltaPDivisionRawRangeEquiv_apply]
  exact RingHom.congr_fun (deltaPDivisionToAway_spec D a₀).2.1 r
end Unary

end SerrePositivity.BhattScholze
