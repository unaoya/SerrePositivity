module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.Comparison.PDFrobeniusLift
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittCrystallinePrism
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittPDBase

/-!
# Witt 基底上の p 正則な分冪包の結晶 prism

## 概要
Witt Frobenius が基底の分冪イデアルを (p) に送ることから、p 正則な分冪包に
結晶 prism の構造を与える。

## 方針
Verschiebung の像には `F(Vx) = px` を使い、多項式変数の Frobenius は p 乗とする。

## 規約
包の台環の p 正則性は仮定として明示する。結晶 prism の生成元は p。

## 使われ方
BS 著者版 Theorem 6.4 の結晶の橋の標的。
-/

public noncomputable section

open WittVector

universe u

namespace SerrePositivity.BhattScholze.Prismatic

variable {p : ℕ} [Fact p.Prime] {C : Type u} [CommRing C]

local notation "W" => WittVector p C

/-- Witt Frobenius は第 0 成分が p の倍数である元を p の倍数へ送る。 -/
theorem wittFrobenius_map_pdIdeal :
    (wittPdIdeal p C).map (WittVector.frobenius : W →+* W) ≤ Ideal.span {(p : W)} := by
  rw [wittPdIdeal_eq_span, Ideal.map_span, Ideal.span_le]
  rintro _ ⟨x, (hx | ⟨v, rfl⟩), rfl⟩
  · obtain rfl := hx
    rw [map_natCast]
    exact Ideal.subset_span (Set.mem_singleton _)
  · rw [frobenius_verschiebung]
    exact Ideal.mul_mem_left _ v (Ideal.subset_span (Set.mem_singleton _))

variable (hpC : Function.Injective (fun x : C => (p : C) * x))
variable (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : C))
variable {σ : Type u} {K : Ideal (MvPolynomial σ (WittVector p C))}
variable (E : CompletedPDEnvelopeData p (wittPdStructure p C hpC hlocal) K)
variable (hreg : Function.Injective (fun x : E.carrier => (p : E.carrier) * x))

local notation "Δ" => wittCrystallineDelta hpC

private theorem wittEnvelope_local (m : ℕ) (hm : ¬p ∣ m) : IsUnit (m : E.carrier) := by
  simpa only [map_natCast] using
    (witt_isUnit_natCast p C m (hlocal m hm)).map (algebraMap W E.carrier)

include hreg in
private theorem exists_wittPDEnvelopeDelta :
    ∃ D : DeltaStructure p E.carrier, (Δ).IsDeltaHom D (algebraMap W E.carrier) ∧
      (∀ i : σ, D.delta (E.unit (MvPolynomial.X i)) = 0) ∧
      E.dividedPowers.IsDPMorphism (residuePdStructure p hreg (wittEnvelope_local hpC hlocal E))
        D.frobeniusLift := by
  apply exists_deltaStructure_of_pdPolynomial Δ _ E hreg
    (fun m hm => witt_isUnit_natCast p C m (hlocal m hm))
  rw [wittCrystallineDelta_frobenius]
  exact wittFrobenius_map_pdIdeal

/-- p 正則な Witt 分冪包の結晶 prism。 -/
def wittPDEnvelopeCrystalline : OrientedPrism p E.carrier :=
  letI := E.isEnvelope.complete
  OrientedPrism.crystalline (exists_wittPDEnvelopeDelta hpC hlocal E hreg).choose hreg

/-- この結晶 prism の生成元は p。 -/
theorem wittPDEnvelopeCrystalline_generator :
    (wittPDEnvelopeCrystalline hpC hlocal E hreg).generator = p := by
  unfold wittPDEnvelopeCrystalline
  rfl

/-- 枠の変数の δ は零。 -/
theorem wittPDEnvelopeCrystalline_delta_X (i : σ) :
    (wittPDEnvelopeCrystalline hpC hlocal E hreg).deltaStructure.delta
      (E.unit (MvPolynomial.X i)) = 0 :=
  (exists_wittPDEnvelopeDelta hpC hlocal E hreg).choose_spec.2.1 i

/-- 包の Frobenius は (p) の標準分冪への分冪射。 -/
theorem wittPDEnvelopeCrystalline_frobenius_isDPMorphism :
    E.dividedPowers.IsDPMorphism (residuePdStructure p hreg (fun m hm => by
      simpa only [map_natCast] using
        (witt_isUnit_natCast p C m (hlocal m hm)).map (algebraMap W E.carrier)))
      (wittPDEnvelopeCrystalline hpC hlocal E hreg).deltaStructure.frobeniusLift :=
  (exists_wittPDEnvelopeDelta hpC hlocal E hreg).choose_spec.2.2

/-- 基底の Witt 結晶 prism から分冪包の結晶 prism への標準射。 -/
def wittPDEnvelopeCrystallineBase [IsAdicComplete (Ideal.span {(p : C)}) C] :
    OrientedPrism.Hom (wittCrystallinePrism hpC) (wittPDEnvelopeCrystalline hpC hlocal E hreg) where
  toRingHom := algebraMap W E.carrier
  map_delta := (exists_wittPDEnvelopeDelta hpC hlocal E hreg).choose_spec.1
  ideal_le := by
    change Ideal.span {(p : W)} ≤ (wittPDEnvelopeCrystalline hpC hlocal E hreg).ideal.comap
      (algebraMap W E.carrier)
    rw [Ideal.span_singleton_le_iff_mem]
    change algebraMap W E.carrier (p : W) ∈ Ideal.span
      {(wittPDEnvelopeCrystalline hpC hlocal E hreg).generator}
    rw [map_natCast, wittPDEnvelopeCrystalline_generator]
    exact Ideal.subset_span (Set.mem_singleton _)

end SerrePositivity.BhattScholze.Prismatic
