module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Envelopes.PDEnvelopeCrystallineMaps
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Envelopes.PDEnvelopeCrystalline
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittPDPrismMaps

/-!
# 完備分冪包の結晶 δ 構造と係数変更

## 概要
係数の δ 射に沿う分冪射は、枠の変数を改名するなら結晶 δ 構造を保つ。

## 方針
二つの Frobenius の合成の基底脚と変数像を照合し、分冪包の一意性を使う。

## 規約
両側の分冪基底の Frobenius 像は (p) に含まれる。

## 使われ方
BS 著者版 Theorem 6.4 の ℤ_p から Witt 係数への小さい結晶模型の変更。
-/

public noncomputable section

universe u

namespace SerrePositivity.BhattScholze.Prismatic

set_option backward.isDefEq.respectTransparency false

variable {p : ℕ} [Fact p.Prime] {k l : Type u} [CommRing k] [CommRing l]
variable (Dk : DeltaStructure p k) (Dl : DeltaStructure p l)
variable {J : Ideal k} {J' : Ideal l} (γ : DividedPowers J) (γ' : DividedPowers J')
variable {S T : Type u} {K : Ideal (MvPolynomial S k)} {K' : Ideal (MvPolynomial T l)}
variable (D : CompletedPDEnvelopeData p γ K) (E : CompletedPDEnvelopeData p γ' K')
variable (hD : Function.Injective (fun x : D.carrier => (p : D.carrier) * x))
variable (hE : Function.Injective (fun x : E.carrier => (p : E.carrier) * x))
variable (hlocalK : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : k))
variable (hlocalL : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : l))
variable (hφK : J.map Dk.frobeniusLift ≤ Ideal.span {(p : k)})
variable (hφL : J'.map Dl.frobeniusLift ≤ Ideal.span {(p : l)})
variable (f : k →+* l) (hfδ : Dk.IsDeltaHom Dl f)
variable (g : D.carrier →+* E.carrier)
variable (hb : g.comp (algebraMap k D.carrier) = (algebraMap l E.carrier).comp f)
variable (hg : D.dividedPowers.IsDPMorphism E.dividedPowers g)
variable (σ : S → T) (hσ : ∀ i, g (D.unit (MvPolynomial.X i)) = E.unit (MvPolynomial.X (σ i)))

local notation "QD" => pdEnvelopeCrystalline Dk γ D hD hlocalK hφK
local notation "QE" => pdEnvelopeCrystalline Dl γ' E hE hlocalL hφL

include hfδ hb hg hσ in
/-- 係数の δ 射に沿って枠を改名する分冪射は、結晶 δ 構造を保つ。 -/
theorem pdEnvelopeCrystalline_coefficient_isDeltaHom :
    (QD).deltaStructure.IsDeltaHom (QE).deltaStructure g := by
  let f₁ := g.comp (QD).deltaStructure.frobeniusLift
  let f₂ := (QE).deltaStructure.frobeniusLift.comp g
  have hb' : f₁.comp (algebraMap k D.carrier) = f₂.comp (algebraMap k D.carrier) := by
    apply RingHom.ext
    intro x
    have hbX (a : k) : g (algebraMap k D.carrier a) = algebraMap l E.carrier (f a) :=
      RingHom.congr_fun hb a
    have hd := (pdEnvelopeCrystalline_base Dk γ D hD hlocalK hφK).map_frobeniusLift x
    have he := (pdEnvelopeCrystalline_base Dl γ' E hE hlocalL hφL).map_frobeniusLift (f x)
    change g ((QD).deltaStructure.frobeniusLift (algebraMap k D.carrier x)) =
      (QE).deltaStructure.frobeniusLift (g (algebraMap k D.carrier x))
    rw [← hd, hbX, hbX]
    exact (congrArg (algebraMap l E.carrier) (hfδ.map_frobeniusLift x)).trans he
  have localD (m : ℕ) (hm : ¬p ∣ m) : IsUnit (m : D.carrier) := by
    simpa only [map_natCast] using (hlocalK m hm).map (algebraMap k D.carrier)
  have localE (m : ℕ) (hm : ¬p ∣ m) : IsUnit (m : E.carrier) := by
    simpa only [map_natCast] using (hlocalL m hm).map (algebraMap l E.carrier)
  let ε := residuePdStructure p hE localE
  have hFD : D.dividedPowers.IsDPMorphism (residuePdStructure p hD localD)
      (QD).deltaStructure.frobeniusLift :=
    (exists_deltaStructure_of_pdPolynomial Dk γ D hD hlocalK hφK).choose_spec.2.2
  have hFE : E.dividedPowers.IsDPMorphism ε (QE).deltaStructure.frobeniusLift :=
    (exists_deltaStructure_of_pdPolynomial Dl γ' E hE hlocalL hφL).choose_spec.2.2
  have h₁ : D.dividedPowers.IsDPMorphism ε f₁ :=
    (isDPMorphism_primeSpan g (residuePdStructure p hD localD) ε hE localE).comp _ hFD
  have h₂ : D.dividedPowers.IsDPMorphism ε f₂ := hFE.comp _ hg
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
  let F₁ : D.carrier →ₐ[k] E.carrier := ⟨f₁, RingHom.congr_fun hb'⟩
  let F₂ : D.carrier →ₐ[k] E.carrier := ⟨f₂, fun _ => rfl⟩
  have heq : F₁ = F₂ := D.isEnvelope.hom_ext hComplete h₁ h₂ (MvPolynomial.algHom_ext hx)
  exact DFunLike.congr_fun heq

end SerrePositivity.BhattScholze.Prismatic
