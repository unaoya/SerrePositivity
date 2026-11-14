module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittPDEnvelopeCrystalline
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittPDEnvelopeCrystalline

/-!
# Witt 分冪包の結晶 prism の射

## 概要
枠の変数を枠の変数へ送る分冪射は、構成した δ 構造を保つ。

## 方針
Frobenius と分冪射の二つの合成を (p) の標準分冪への射とみなす。
係数と変数で一致することから分冪包の普遍性を適用する。

## 規約
標的の p 正則性で Frobenius との可換性から δ との可換性を得る。

## 使われ方
BS 著者版 Theorem 6.4 の大きい Witt 枠の代入と単体の射。
-/

public noncomputable section

universe u

namespace SerrePositivity.BhattScholze.Prismatic

set_option backward.isDefEq.respectTransparency false

section Principal

variable {p : ℕ} [Fact p.Prime] {D E : Type u} [CommRing D] [CommRing E]

private theorem isDPMorphism_primeSpan (g : D →+* E)
    (δ : DividedPowers (Ideal.span {(p : D)})) (ε : DividedPowers (Ideal.span {(p : E)}))
    (hreg : Function.Injective (fun x : E => (p : E) * x))
    (hloc : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : E)) : δ.IsDPMorphism ε g := by
  have hI : (Ideal.span {(p : D)}).map g ≤ Ideal.span {(p : E)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  refine ⟨hI, fun {n} x hx => ?_⟩
  let L := Localization.Away (p : E)
  let a := algebraMap E L
  let : Algebra ℚ L := DeltaStructure.primeDividedPowersAwayRatAlgebra hloc
  apply away_injective_of_prime p hreg
  apply (IsUnit.natCast_factorial_of_algebra ℚ n (A := L)).mul_left_cancel
  have h₁ := congrArg (a.comp g) (δ.factorial_mul_dpow_eq_pow (n := n) hx)
  have h₂ := congrArg a (ε.factorial_mul_dpow_eq_pow (n := n) (hI (Ideal.mem_map_of_mem g hx)))
  simp only [RingHom.comp_apply, map_mul, map_natCast, map_pow] at h₁ h₂
  exact h₂.trans h₁.symm

end Principal

section Witt

variable {p : ℕ} [Fact p.Prime] {C : Type u} [CommRing C]

local notation "W" => WittVector p C
variable (hpC : Function.Injective (fun x : C => (p : C) * x))
variable (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : C))
variable [IsAdicComplete (Ideal.span {(p : C)}) C]

variable {S T : Type u} {K : Ideal (MvPolynomial S (WittVector p C))}
  {K' : Ideal (MvPolynomial T (WittVector p C))}
variable (D : CompletedPDEnvelopeData p (wittPdStructure p C hpC hlocal) K)
variable (E : CompletedPDEnvelopeData p (wittPdStructure p C hpC hlocal) K')
variable (hD : Function.Injective (fun x : D.carrier => (p : D.carrier) * x))
variable (hE : Function.Injective (fun x : E.carrier => (p : E.carrier) * x))

local notation "prismD" => wittPDEnvelopeCrystalline hpC hlocal D hD
local notation "prismE" => wittPDEnvelopeCrystalline hpC hlocal E hE

variable (g : D.carrier →ₐ[WittVector p C] E.carrier)
variable (hg : D.dividedPowers.IsDPMorphism E.dividedPowers g.toRingHom)
variable (σ : S → T) (hσ : ∀ i, g (D.unit (MvPolynomial.X i)) = E.unit (MvPolynomial.X (σ i)))

include hg hσ in
/-- 枠の変数を改名する Witt 係数の分冪射は結晶 δ 構造を保つ。 -/
theorem wittPDEnvelopeCrystalline_isDeltaHom :
    (prismD).deltaStructure.IsDeltaHom (prismE).deltaStructure g.toRingHom := by
  let f₁ := g.toRingHom.comp (prismD).deltaStructure.frobeniusLift
  let f₂ := (prismE).deltaStructure.frobeniusLift.comp g.toRingHom
  have hb : f₁.comp (algebraMap W D.carrier) = f₂.comp (algebraMap W D.carrier) := by
    apply RingHom.ext
    intro x
    change g ((prismD).deltaStructure.frobeniusLift (algebraMap W D.carrier x)) =
      (prismE).deltaStructure.frobeniusLift (g (algebraMap W D.carrier x))
    have hd := (wittPDEnvelopeCrystallineBase hpC hlocal D hD).map_delta.map_frobeniusLift x
    have he := (wittPDEnvelopeCrystallineBase hpC hlocal E hE).map_delta.map_frobeniusLift x
    change algebraMap W D.carrier ((wittCrystallinePrism hpC).deltaStructure.frobeniusLift x) =
      (prismD).deltaStructure.frobeniusLift (algebraMap W D.carrier x) at hd
    change algebraMap W E.carrier ((wittCrystallinePrism hpC).deltaStructure.frobeniusLift x) =
      (prismE).deltaStructure.frobeniusLift (algebraMap W E.carrier x) at he
    rw [g.commutes, ← hd, ← he, g.commutes]
  let ε := residuePdStructure p hE (wittEnvelope_local hpC hlocal E)
  have he : D.dividedPowers.IsDPMorphism ε f₂ :=
    (wittPDEnvelopeCrystalline_frobenius_isDPMorphism hpC hlocal E hE).comp _ hg
  have hd : D.dividedPowers.IsDPMorphism ε f₁ :=
    (isDPMorphism_primeSpan g.toRingHom (residuePdStructure p hD
      (wittEnvelope_local hpC hlocal D)) ε hE (wittEnvelope_local hpC hlocal E)).comp _
      (wittPDEnvelopeCrystalline_frobenius_isDPMorphism hpC hlocal D hD)
  have hx (i : S) : f₁ (D.unit (MvPolynomial.X i)) = f₂ (D.unit (MvPolynomial.X i)) := by
    change g ((prismD).deltaStructure.frobeniusLift (D.unit (MvPolynomial.X i))) =
      (prismE).deltaStructure.frobeniusLift (g (D.unit (MvPolynomial.X i)))
    rw [hσ, DeltaStructure.frobeniusLift_apply, DeltaStructure.frobeniusLift_apply,
      wittPDEnvelopeCrystalline_delta_X, wittPDEnvelopeCrystalline_delta_X,
      mul_zero, add_zero, mul_zero, add_zero, map_pow, hσ]
  apply DeltaStructure.isDeltaHom_of_map_frobeniusLift _ hE
  have hComplete := E.isEnvelope.complete
  let a : W →+* E.carrier := f₂.comp (algebraMap W D.carrier)
  let : Algebra W E.carrier := a.toAlgebra
  let F₁ : D.carrier →ₐ[W] E.carrier := ⟨f₁, RingHom.congr_fun hb⟩
  let F₂ : D.carrier →ₐ[W] E.carrier := ⟨f₂, fun _ => rfl⟩
  have heq : F₁ = F₂ :=
    D.isEnvelope.hom_ext hComplete hd he (MvPolynomial.algHom_ext hx)
  exact DFunLike.congr_fun heq

end Witt

end SerrePositivity.BhattScholze.Prismatic
