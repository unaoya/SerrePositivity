module

public import SerrePositivity.BhattScholze.PerfectDeltaFrobeniusQuotientSquare
public import SerrePositivity.BhattScholze.PerfectDeltaPrismaticDerivedFlat

/-! # 実Frobeniusねじれ段の標準prism還元の次数消滅と忠実平坦性 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

section General
variable (D : DeltaStructure p A) (hD : D.IsPerfect) (d : A) (n : ℕ)
variable (X : DerivedCategory.Minus (ModuleCat.{u} A))
local notation "Q₀" => A ⧸ Ideal.span {(p : A), d}
local notation "Qₙ" => A ⧸ Ideal.span {(p : A), (D.frobeniusLift ^ n) d}
local notation "κ" => RingEquiv.toRingHom
  (perfectDeltaFrobeniusPrismaticResidueEquiv D hD d n)
local notation "Y₀" => CategoryTheory.Functor.obj
  (boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {(p : A), d}))) X
local notation "Yₙ" => CategoryTheory.Functor.obj
  (boundedAboveDerivedBaseChange
    (Ideal.Quotient.mk (Ideal.span {(p : A), (D.frobeniusLift ^ n) d}))) X
local notation "Zₙ" => CategoryTheory.Functor.obj
  (boundedAboveDerivedRestrictScalars (D.frobeniusLift ^ n)) X
local notation "Wₙ" => CategoryTheory.Functor.obj
  (boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {(p : A), d}))) Zₙ
include hD

/-- 実ねじれ段の標準還元のホモロジーと、移動係数還元の正確な係数制限。 -/
def perfectDeltaFrobeniusTwistResidueHomologyIso (i : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat Q₀) i).obj (Wₙ).obj ≅
      (ModuleCat.restrictScalars κ).obj
        ((DerivedCategory.homologyFunctor (ModuleCat Qₙ) i).obj (Yₙ).obj) :=
  (DerivedCategory.homologyFunctor (ModuleCat Q₀) i).mapIso
      (DerivedCategory.Minus.ι.mapIso
        (perfectDeltaFrobeniusQuotientDerivedIso D hD d n X
          (boundedAboveDerivedChosenModel X))) ≪≫
    (derivedRestrictScalarsHomologyIso κ i).app (Yₙ).obj

/-- 元の実標準還元の性質から、ねじれ段の実標準還元の次数消滅を得る。 -/
theorem perfectDeltaFrobeniusTwistResidue_homology_isZero
    (hzero : ∀ i : ℤ, i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q₀) i).obj (Y₀).obj))
    (hFF : Module.FaithfullyFlat Q₀
      ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj (Y₀).obj))
    (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q₀) i).obj (Wₙ).obj) := by
  obtain ⟨hGE, hLE, _⟩ :=
    frobeniusPrismaticDerivedReduction_pure_faithfullyFlat D d n X hzero hFF
  have hz : IsZero ((DerivedCategory.homologyFunctor (ModuleCat Qₙ) i).obj (Yₙ).obj) := by
    rcases lt_or_gt_of_ne hi with h | h
    · exact (DerivedCategory.isGE_iff _ _).mp hGE i h
    · exact (DerivedCategory.isLE_iff _ _).mp hLE i h
  exact ((ModuleCat.restrictScalars κ).map_isZero hz).of_iso
    (perfectDeltaFrobeniusTwistResidueHomologyIso D hD d n X i)

/-- ねじれ段の実標準還元のH0は、同じ元のA/(p,d)上で忠実平坦。 -/
theorem perfectDeltaFrobeniusTwistResidueH0_faithfullyFlat
    (hzero : ∀ i : ℤ, i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q₀) i).obj (Y₀).obj))
    (hFF : Module.FaithfullyFlat Q₀
      ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj (Y₀).obj)) :
    Module.FaithfullyFlat Q₀
      ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj (Wₙ).obj) := by
  let M := (ModuleCat.restrictScalars κ).obj
    ((DerivedCategory.homologyFunctor (ModuleCat Qₙ) 0).obj (Yₙ).obj)
  have : Module.FaithfullyFlat Q₀ M :=
    perfectDeltaFrobeniusResidueH0_faithfullyFlat D d n X hD hzero hFF
  exact Module.FaithfullyFlat.of_linearEquiv Q₀ M
    (perfectDeltaFrobeniusTwistResidueHomologyIso D hD d n X 0).toLinearEquiv
end General

/-- 完全prismの有限根族の実逐次源について、全実ねじれ段の標準還元入力。 -/
theorem perfectPrismRootFamilySource_frobenius_twist_inputs
    {σ : Type u} (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect)
    (b : σ → A) {m : ℕ} (s : Fin m ≃ σ) (k : ℕ) :
    let D := P.deltaStructure
    let d := P.generator
    let X := DeltaRootSourceIteratedPDCompletion D d b
    let Z := (boundedAboveDerivedRestrictScalars (D.frobeniusLift ^ k)).obj X
    let Q := A ⧸ Ideal.span {(p : A), d}
    let Y := (boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {(p : A), d}))).obj Z
    (∀ i : ℤ, i ≠ 0 → IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q) i).obj Y.obj)) ∧
      Module.FaithfullyFlat Q
        ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj Y.obj) := by
  let X := DeltaRootSourceIteratedPDCompletion P.deltaStructure P.generator b
  have hz := perfectPrismRootFamilySource_modPD_homology_isZero P hP b s
  have hf := perfectPrismRootFamilySource_modPDH0_faithfullyFlat P hP b s
  exact ⟨perfectDeltaFrobeniusTwistResidue_homology_isZero
      P.deltaStructure hP P.generator k X hz hf,
    perfectDeltaFrobeniusTwistResidueH0_faithfullyFlat P.deltaStructure hP P.generator k X hz hf⟩

end SerrePositivity.BhattScholze
