module

public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.DeltaRoot.DeltaRootFamilySourceCanonicalPowerResidue
public import SerrePositivity.BhattScholze.Prism.Residue.PrismaticGeneratorPowerModP
public import SerrePositivity.BhattScholze.Semiperfectoid.RootEnvelope.Source.DeltaRootSourceGeneratorPowerComplete
public import SerrePositivity.HomologicalAlgebra.NilpotentDerivedReduction

/-! # 有限根族のG10と生成元冪商上の標準G9入力 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (b : σ → A) (n : ℕ) (hn : 0 < n)
variable {m : ℕ} (s : Fin m ≃ σ)
variable (hpA : Function.Injective (fun x : A => (p : A) * x))
  (hd : IsSMulRegular A d) (v : Aˣ) (hv : (v : A) = D.delta d)
local notation "Qₙ" => A ⧸ Ideal.span {(p : A), d ^ n}
local notation "Kₙ" => prismaticPowerResidueIdeal (p : A) d n
local notation "X₀" => DeltaRootSourceIteratedPDCompletion D d b
local notation "Y₀" => CategoryTheory.Functor.obj
  (boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {(p : A), d ^ n}))) X₀
local notation "Tₙ" => A ⧸ Ideal.span {d ^ n}
local notation "Mₙ" => Tₙ ⧸ Ideal.span {(p : Tₙ)}
local notation "Zₙ" => CategoryTheory.Functor.obj
  (boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {d ^ n}))) X₀
local notation "Wₙ" => CategoryTheory.Functor.obj
  (boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {(p : Tₙ)}))) Zₙ
include hn s hpA hd v hv

/-- G10により、実A/(p,dⁿ)還元は次数零に集中しH0が平坦。 -/
theorem deltaRootFamilySourcePowerResidue_pure_flat :
    (Y₀).obj.IsGE 0 ∧ (Y₀).obj.IsLE 0 ∧
      Module.Flat Qₙ ((DerivedCategory.homologyFunctor (ModuleCat Qₙ) 0).obj (Y₀).obj) := by
  have hPure := deltaRootFamilySourceCanonicalPowerResidue_homology_isZero
    D d b n hn s hpA hd v hv
  have hFF := deltaRootFamilySourceCanonicalPowerResidueH0_faithfullyFlat
    D d b n hn s hpA hd v hv
  let := hFF
  exact derived_pure_flat_of_nilpotent_reduction Kₙ Y₀ hPure
    inferInstance ⟨n, prismaticPowerResidueIdeal_pow (p : A) d n⟩

/-- G10で得た実冪剰余の非零次数ホモロジー消滅。 -/
theorem deltaRootFamilySourcePowerResidue_homology_isZero (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat Qₙ) i).obj (Y₀).obj) := by
  obtain ⟨hGE, hLE, _⟩ :=
    deltaRootFamilySourcePowerResidue_pure_flat D d b n hn s hpA hd v hv
  rcases lt_or_gt_of_ne hi with h | h
  · exact (DerivedCategory.isGE_iff _ _).mp hGE i h
  · exact (DerivedCategory.isLE_iff _ _).mp hLE i h

/-- 同じ実冪剰余のH0平坦性。 -/
theorem deltaRootFamilySourcePowerResidueH0_flat :
    Module.Flat Qₙ ((DerivedCategory.homologyFunctor (ModuleCat Qₙ) 0).obj (Y₀).obj) :=
  (deltaRootFamilySourcePowerResidue_pure_flat D d b n hn s hpA hd v hv).2.2

/-- A/(dⁿ)上の標準mod p実還元の非零次数ホモロジー消滅。 -/
theorem deltaRootFamilySourceGeneratorPowerModP_homology_isZero (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat Mₙ) i).obj (Wₙ).obj) :=
  prismaticGeneratorPowerModP_homology_isZero p d n X₀ i
    (deltaRootFamilySourcePowerResidue_homology_isZero D d b n hn s hpA hd v hv i hi)

/-- 標準mod p実還元のH0は、その正確な商環上で平坦。 -/
theorem deltaRootFamilySourceGeneratorPowerModPH0_flat :
    Module.Flat Mₙ ((DerivedCategory.homologyFunctor (ModuleCat Mₙ) 0).obj (Wₙ).obj) :=
  prismaticGeneratorPowerModPH0_flat p d n X₀
    (deltaRootFamilySourcePowerResidueH0_flat D d b n hn s hpA hd v hv)

/-- G8の商上完備性とG10の実mod p入力を、G9用の同じ対象で束ねる。 -/
theorem deltaRootFamilySourceGeneratorPower_G9_inputs :
    DerivedCompletion.IsComplete Tₙ (p : Tₙ) (Zₙ).obj ∧
      (∀ i : ℤ, i ≠ 0 →
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat Mₙ) i).obj (Wₙ).obj)) ∧
      Module.Flat Mₙ ((DerivedCategory.homologyFunctor (ModuleCat Mₙ) 0).obj (Wₙ).obj) := by
  exact ⟨deltaRootSourceGeneratorPowerReduction_isComplete_over_quotient D d b hd n,
    deltaRootFamilySourceGeneratorPowerModP_homology_isZero D d b n hn s hpA hd v hv,
    deltaRootFamilySourceGeneratorPowerModPH0_flat D d b n hn s hpA hd v hv⟩

end SerrePositivity.BhattScholze
