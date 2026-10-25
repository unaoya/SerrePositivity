module

public import SerrePositivity.BhattScholze.Delta.DividedPower.DeltaPDivisionWittResidueEvaluation
public import SerrePositivity.BhattScholze.RootedExtension.Division.DeltaPDivisionRawRegular
public import SerrePositivity.BhattScholze.Delta.Division.DeltaDivisionPDCompletion

/-! # 正則な一元p除算の実導来完備化からの通常剰余射

元の係数射がp,yを消す場合を扱う。raw包のp正則性の仮定を明示して
旧ねじれ除去商を経由し、実H⁰から環として延長する。
一般の導来Koszul代数への射・CFF・prism性は結論しない。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open SerrePositivity.DerivedCompletion
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (D : DeltaStructure p A) (y : A)
variable (hpA : Function.Injective (fun x : A ↦ (p : A) * x))
variable (hgA : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A))
variable (hgL : Function.Injective (WittVector.ghostMap :
  WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
variable (v : Aˣ) (hv : (v : A) = D.delta (p : A))
variable (hy : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
  (Ideal.Quotient.mk (Ideal.span {(p : A)}) y))
attribute [local instance] derivedDeltaDivisionCommRing
local notation "a₀" => fun _ : σ ↦ D.frobeniusLift y
local notation "R₀" => DeltaDivisionTorsionQuotient D (p : A) a₀
local notation "B₀" => DeltaAdjoinDivision D (p : A) a₀
local notation "H₀" => DerivedDeltaDivisionCompletion D (p : A) a₀
local notation "j₀" => deltaDivisionTorsionMap D (p : A) a₀
local notation "u₀" => pdCompletionUnit R₀ p (j₀ (p : A))
local notation "k₀" => derivedDeltaDivisionMap D (p : A) a₀

section General
variable {B : Type u} [CommRing B] (q : A →+* B) (hqy : q y = 0)

/-- raw/旧ねじれ除去商同型を使って、具体的通常評価を既存商へ因子化する。 -/
def deltaPDivisionTorsionResidueMap : R₀ →+* B :=
  (deltaPDivisionWittResidueMap D hpA q (fun _ : σ ↦ y) hgA hgL (fun _ ↦ hqy)).comp
    (deltaPDivisionRawTorsionEquiv (σ := σ) D y hpA hgL v hv hy).symm.toRingHom

/-- 因子化は実際の旧ねじれ除去標準商射と両立する。 -/
theorem deltaPDivisionTorsionResidueMap_comp_raw :
    (deltaPDivisionTorsionResidueMap D y hpA hgA hgL v hv hy q hqy).comp
      (Ideal.Quotient.mk ((deltaAdjoinDivisionStructure D (p : A) a₀).deltaClosure
        (RingHom.ker (algebraMap B₀ (Localization.Away
          (deltaAdjoinDivisionMap D (p : A) a₀ (p : A))))))) =
      deltaPDivisionWittResidueMap D hpA q (fun _ : σ ↦ y) hgA hgL (fun _ ↦ hqy) := by
  let e := deltaPDivisionRawTorsionEquiv (σ := σ) D y hpA hgL v hv hy
  apply RingHom.ext
  intro b
  change deltaPDivisionWittResidueMap D hpA q (fun _ : σ ↦ y) hgA hgL (fun _ ↦ hqy)
    (e.symm (Ideal.Quotient.mk _ b)) = _
  have he : e b = Ideal.Quotient.mk _ b :=
    deltaPDivisionRawTorsionEquiv_apply (σ := σ) D y hpA hgL v hv hy b
  rw [← he, RingEquiv.symm_apply_apply]

/-- 旧ねじれ除去商からの通常剰余射は、元の係数射qを保つ。 -/
theorem deltaPDivisionTorsionResidueMap_comp_base :
    (deltaPDivisionTorsionResidueMap D y hpA hgA hgL v hv hy q hqy).comp j₀ = q := by
  change (deltaPDivisionTorsionResidueMap D y hpA hgA hgL v hv hy q hqy).comp
    ((Ideal.Quotient.mk _).comp (deltaAdjoinDivisionMap D (p : A) a₀)) = q
  rw [← RingHom.comp_assoc, deltaPDivisionTorsionResidueMap_comp_raw,
    deltaPDivisionWittResidueMap_comp_base]

private theorem complete_of_zero_scalar (b : B) (hb : b = 0) :
    IsModuleComplete B b (ModuleCat.of B B) := by
  apply isModuleComplete_of_pow_smul_zero B b (ModuleCat.of B B) 1
  intro x
  rw [pow_one, hb, zero_smul]

variable (hqp : q (p : A) = 0)
include hqp

/-- p,yを消す係数射への通常剰余射は、実導来完備化H⁰から一意に延長する。 -/
theorem existsUnique_deltaPDivisionDerivedResidueMap :
    ∃! f : H₀ →+* B, f.comp u₀ =
      deltaPDivisionTorsionResidueMap D y hpA hgA hgL v hv hy q hqy := by
  have hpB : (p : B) = 0 := (map_natCast q p).symm.trans hqp
  have hdB : deltaPDivisionTorsionResidueMap D y hpA hgA hgL v hv hy q hqy
      (j₀ (p : A)) = 0 :=
    (RingHom.congr_fun (deltaPDivisionTorsionResidueMap_comp_base D y hpA hgA hgL v hv hy q hqy)
      (p : A)).trans hqp
  exact existsUnique_pdCompletionRingHom R₀ p (j₀ (p : A)) B
    (deltaPDivisionTorsionResidueMap D y hpA hgA hgL v hv hy q hqy)
    (complete_of_zero_scalar (p : B) hpB) (complete_of_zero_scalar _ hdB)

/-- 実導来完備化H⁰から、p,yを消す具体的係数射の終域への通常環射。 -/
def deltaPDivisionDerivedResidueMap : H₀ →+* B :=
  (existsUnique_deltaPDivisionDerivedResidueMap D y hpA hgA hgL v hv hy q hqy hqp).choose

/-- 実H⁰からの射は旧ねじれ除去商の実Koszul標準単位と両立する。 -/
theorem deltaPDivisionDerivedResidueMap_comp_unit :
    (deltaPDivisionDerivedResidueMap D y hpA hgA hgL v hv hy q hqy hqp).comp u₀ =
      deltaPDivisionTorsionResidueMap D y hpA hgA hgL v hv hy q hqy :=
  (existsUnique_deltaPDivisionDerivedResidueMap D y hpA hgA hgL v hv hy q hqy hqp).choose_spec.1

/-- 実H⁰からの射と元のAからの標準射の合成はq。 -/
theorem deltaPDivisionDerivedResidueMap_comp_base :
    (deltaPDivisionDerivedResidueMap D y hpA hgA hgL v hv hy q hqy hqp).comp k₀ = q := by
  change (deltaPDivisionDerivedResidueMap D y hpA hgA hgL v hv hy q hqy hqp).comp
    ((u₀).comp j₀) = q
  rw [← RingHom.comp_assoc, deltaPDivisionDerivedResidueMap_comp_unit,
    deltaPDivisionTorsionResidueMap_comp_base]

/-- 元の係数射が全射なら、この具体的通常剰余射も全射。 -/
theorem deltaPDivisionDerivedResidueMap_surjective (hq : Function.Surjective q) :
    Function.Surjective (deltaPDivisionDerivedResidueMap D y hpA hgA hgL v hv hy q hqy hqp) := by
  intro b
  obtain ⟨r, hr⟩ := hq b
  exact ⟨k₀ r, (RingHom.congr_fun
    (deltaPDivisionDerivedResidueMap_comp_base D y hpA hgA hgL v hv hy q hqy hqp) r).trans hr⟩
end General

/-- 実導来完備化からA/(p,y)への具体的通常環射。 -/
def deltaPDivisionDerivedResidueQuotientMap : H₀ →+* (A ⧸ Ideal.span {(p : A), y}) :=
  deltaPDivisionDerivedResidueMap (σ := σ) D y hpA hgA hgL v hv hy
    (Ideal.Quotient.mk (Ideal.span {(p : A), y}))
    (Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
    (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_insert _ _)))

/-- 具体的剰余射はAからの標準商写像を延長する。 -/
theorem deltaPDivisionDerivedResidueQuotientMap_comp_base :
    (deltaPDivisionDerivedResidueQuotientMap (σ := σ) D y hpA hgA hgL v hv hy).comp k₀ =
      Ideal.Quotient.mk (Ideal.span {(p : A), y}) :=
  deltaPDivisionDerivedResidueMap_comp_base D y hpA hgA hgL v hv hy _ _ _

/-- 実H⁰からA/(p,y)への具体的通常剰余射は全射。 -/
theorem deltaPDivisionDerivedResidueQuotientMap_surjective :
    Function.Surjective
      (deltaPDivisionDerivedResidueQuotientMap (σ := σ) D y hpA hgA hgL v hv hy) :=
  deltaPDivisionDerivedResidueMap_surjective D y hpA hgA hgL v hv hy _ _ _
    Ideal.Quotient.mk_surjective

end SerrePositivity.BhattScholze
