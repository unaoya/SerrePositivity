module

public import SerrePositivity.BhattScholze.Andre.RootedExtension.DeltaRoot.DeltaRootFamilySourceIteratedResidue
public import SerrePositivity.BhattScholze.Andre.RootedExtension.DeltaRoot.DeltaRootSourceIteratedCompletionComplete
public import SerrePositivity.BhattScholze.Prism.Basic.OrientedPrism

/-! # 完全prismから有限根族の実逐次完備化源への入力 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect) (b : σ → A)
variable {m : ℕ} (s : Fin m ≃ σ)
local notation "D" => OrientedPrism.deltaStructure P
local notation "d" => OrientedPrism.generator P
local notation "Q₀" => A ⧸ Ideal.span {(p : A), d}
local notation "q₀" => Ideal.Quotient.mk (Ideal.span {(p : A), d})
local notation "X₀" => DeltaRootSourceIteratedPDCompletion D d b
local notation "Y₀" => CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange q₀) X₀
include hP

private theorem generatorRegular : IsSMulRegular A d := by
  let := P.isAdicComplete_p_of_perfect hP
  exact hP.distinguished_mul_injective (P.isDistinguished_of_perfect hP)

include s

/-- 完全prismから、有限根族の実逐次源の実(p,d)還元の非零次数消滅を得る。 -/
theorem perfectPrismRootFamilySource_modPD_homology_isZero (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q₀) i).obj (Y₀).obj) := by
  obtain ⟨v, hv⟩ := P.isDistinguished_of_perfect hP
  exact deltaRootFamilySourceIteratedPDResidue_homology_isZero D d b s hP.p_mul_injective
    (generatorRegular P hP) v hv i hi

/-- 同じ実還元のH0は、元のA/(p,d)上で忠実平坦。追加単元・ghost入力は不要。 -/
theorem perfectPrismRootFamilySource_modPDH0_faithfullyFlat :
    Module.FaithfullyFlat Q₀ ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj (Y₀).obj) := by
  obtain ⟨v, hv⟩ := P.isDistinguished_of_perfect hP
  exact deltaRootFamilySourceIteratedPDResidueH0_faithfullyFlat D d b s hP.p_mul_injective
    (generatorRegular P hP) v hv

/-- 元の同じ実逐次源のp,d完備性と実(p,d)還元の消滅・忠実平坦性を束ねる。 -/
theorem perfectPrismRootFamilySource_complete_residue_inputs :
    DerivedCompletion.IsComplete A (p : A) (X₀).obj ∧
      DerivedCompletion.IsComplete A d (X₀).obj ∧
      (∀ i : ℤ, i ≠ 0 →
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q₀) i).obj (Y₀).obj)) ∧
      Module.FaithfullyFlat Q₀
        ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj (Y₀).obj) := by
  exact ⟨deltaRootSourceIteratedPDCompletion_isComplete_p D d b,
    deltaRootSourceIteratedPDCompletion_isComplete_d D d b,
    perfectPrismRootFamilySource_modPD_homology_isZero P hP b s,
    perfectPrismRootFamilySource_modPDH0_faithfullyFlat P hP b s⟩

end SerrePositivity.BhattScholze
