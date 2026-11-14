module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Envelopes.PDEnvelopeCrystalline
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittPDPrismMaps
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittPDPrismMaps
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Envelopes.PDEnvelopeCrystalline

/-!
# 完備分冪包の結晶 δ 構造と枠の改名

## 概要
基底を固定して枠の変数を改名する分冪射は、結晶 δ 構造を保つ。

## 方針
Frobenius との二つの合成を分冪包の普遍性で比較し、標的の p 正則性を使う。

## 規約
基底の分冪イデアルの Frobenius 像が (p) に含まれることを仮定する。

## 使われ方
BS 著者版 Theorems 5.2・6.4 の小さい結晶模型の余単体構造。
-/

public noncomputable section

universe u

namespace SerrePositivity.BhattScholze.Prismatic

set_option backward.isDefEq.respectTransparency false

variable {p : ℕ} [Fact p.Prime] {k : Type u} [CommRing k]
variable (Dk : DeltaStructure p k) {J : Ideal k} (γ : DividedPowers J)
variable {S T : Type u} {K : Ideal (MvPolynomial S k)} {K' : Ideal (MvPolynomial T k)}
variable (D : CompletedPDEnvelopeData p γ K) (E : CompletedPDEnvelopeData p γ K')
variable (hD : Function.Injective (fun x : D.carrier => (p : D.carrier) * x))
variable (hE : Function.Injective (fun x : E.carrier => (p : E.carrier) * x))
variable (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : k))
variable (hφ : J.map Dk.frobeniusLift ≤ Ideal.span {(p : k)})

local notation "QD" => pdEnvelopeCrystalline Dk γ D hD hlocal hφ
local notation "QE" => pdEnvelopeCrystalline Dk γ E hE hlocal hφ

omit [Fact p.Prime] in
include hlocal in
private theorem carrier_local (m : ℕ) (hm : ¬p ∣ m) : IsUnit (m : E.carrier) := by
  simpa only [map_natCast] using (hlocal m hm).map (algebraMap k E.carrier)

private theorem frobenius_dp :
    E.dividedPowers.IsDPMorphism (residuePdStructure p hE (carrier_local γ E hlocal))
      (QE).deltaStructure.frobeniusLift :=
  (exists_deltaStructure_of_pdPolynomial Dk γ E hE hlocal hφ).choose_spec.2.2

variable (g : D.carrier →ₐ[k] E.carrier)
variable (hg : D.dividedPowers.IsDPMorphism E.dividedPowers g.toRingHom)
variable (σ : S → T) (hσ : ∀ i, g (D.unit (MvPolynomial.X i)) = E.unit (MvPolynomial.X (σ i)))

include hg hσ in
/-- 変数を改名する基底上の分冪射は結晶 δ 構造を保つ。 -/
theorem pdEnvelopeCrystalline_isDeltaHom :
    (QD).deltaStructure.IsDeltaHom (QE).deltaStructure g.toRingHom := by
  let f₁ := g.toRingHom.comp (QD).deltaStructure.frobeniusLift
  let f₂ := (QE).deltaStructure.frobeniusLift.comp g.toRingHom
  have hb : f₁.comp (algebraMap k D.carrier) = f₂.comp (algebraMap k D.carrier) := by
    apply RingHom.ext
    intro x
    change g ((QD).deltaStructure.frobeniusLift (algebraMap k D.carrier x)) =
      (QE).deltaStructure.frobeniusLift (g (algebraMap k D.carrier x))
    have hd := (pdEnvelopeCrystalline_base Dk γ D hD hlocal hφ).map_frobeniusLift x
    have he := (pdEnvelopeCrystalline_base Dk γ E hE hlocal hφ).map_frobeniusLift x
    rw [g.commutes, ← hd, ← he, g.commutes]
  let ε := residuePdStructure p hE (carrier_local γ E hlocal)
  have he : D.dividedPowers.IsDPMorphism ε f₂ :=
    (frobenius_dp Dk γ E hE hlocal hφ).comp _ hg
  have hd : D.dividedPowers.IsDPMorphism ε f₁ :=
    (isDPMorphism_primeSpan g.toRingHom (residuePdStructure p hD (carrier_local γ D hlocal))
      ε hE (carrier_local γ E hlocal)).comp _ (frobenius_dp Dk γ D hD hlocal hφ)
  have hx (i : S) : f₁ (D.unit (MvPolynomial.X i)) = f₂ (D.unit (MvPolynomial.X i)) := by
    change g ((QD).deltaStructure.frobeniusLift (D.unit (MvPolynomial.X i))) =
      (QE).deltaStructure.frobeniusLift (g (D.unit (MvPolynomial.X i)))
    rw [hσ, DeltaStructure.frobeniusLift_apply, DeltaStructure.frobeniusLift_apply,
      pdEnvelopeCrystalline_delta_X, pdEnvelopeCrystalline_delta_X,
      mul_zero, add_zero, mul_zero, add_zero, map_pow, hσ]
  apply DeltaStructure.isDeltaHom_of_map_frobeniusLift _ hE
  have hComplete := E.isEnvelope.complete
  let a : k →+* E.carrier := f₂.comp (algebraMap k D.carrier)
  let : Algebra k E.carrier := a.toAlgebra
  let F₁ : D.carrier →ₐ[k] E.carrier := ⟨f₁, RingHom.congr_fun hb⟩
  let F₂ : D.carrier →ₐ[k] E.carrier := ⟨f₂, fun _ => rfl⟩
  have heq : F₁ = F₂ :=
    D.isEnvelope.hom_ext hComplete hd he (MvPolynomial.algHom_ext hx)
  exact DFunLike.congr_fun heq

end SerrePositivity.BhattScholze.Prismatic
