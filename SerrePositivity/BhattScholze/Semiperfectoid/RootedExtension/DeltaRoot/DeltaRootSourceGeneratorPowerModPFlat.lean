module

public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.DeltaRoot.DeltaRootSourcePowerResidueFaithful
public import SerrePositivity.BhattScholze.Prism.Residue.PrismaticGeneratorPowerModP
public import SerrePositivity.BhattScholze.Semiperfectoid.RootEnvelope.Source.DeltaRootSourceGeneratorPowerComplete

/-! # G9へ渡す実生成元冪商の標準mod p入力 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (D : DeltaStructure p A) (d : A) (b : σ → A) (n : ℕ) (hn : 0 < n)
variable (hpA : Function.Injective (fun x : A => (p : A) * x))
  (hd : IsSMulRegular A d) (v : Aˣ) (hv : (v : A) = D.delta d)
local notation "Tₙ" => A ⧸ Ideal.span (Set.singleton (d ^ n))
local notation "Mₙ" => Tₙ ⧸ Ideal.span (Set.singleton (p : Tₙ))
local notation "X₀" => DeltaRootSourceIteratedPDCompletion D d b
local notation "Zₙ" => CategoryTheory.Functor.obj
  (boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span (Set.singleton (d ^ n))))) X₀
local notation "Wₙ" => CategoryTheory.Functor.obj
  (boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span (Set.singleton (p : Tₙ))))) Zₙ

include hn hpA hd v hv in
/-- 商環Tₙ上の標準mod p実還元は、非零次数のホモロジーが消える。 -/
theorem deltaRootSourceGeneratorPowerModP_homology_isZero (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat Mₙ) i).obj (Wₙ).obj) :=
  prismaticGeneratorPowerModP_homology_isZero p d n X₀ i
    (deltaRootSourcePowerResidue_homology_isZero D d b n hn hpA hd v hv i hi)

include hn hpA hd v hv in
/-- 標準mod p実還元のH0は、正確な標準商環Tₙ/p上で平坦。 -/
theorem deltaRootSourceGeneratorPowerModPH0_flat :
    Module.Flat Mₙ ((DerivedCategory.homologyFunctor (ModuleCat Mₙ) 0).obj (Wₙ).obj) :=
  prismaticGeneratorPowerModPH0_flat p d n X₀
    (deltaRootSourcePowerResidueH0_flat D d b n hn hpA hd v hv)

include hn hpA hd v hv in
/-- G9へ渡す実Tₙ対象のp完備性と、標準mod p還元の離散・平坦性。 -/
theorem deltaRootSourceGeneratorPower_G9_inputs :
    DerivedCompletion.IsComplete Tₙ (p : Tₙ) (Zₙ).obj ∧
      (∀ i : ℤ, i ≠ 0 →
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat Mₙ) i).obj (Wₙ).obj)) ∧
      Module.Flat Mₙ ((DerivedCategory.homologyFunctor (ModuleCat Mₙ) 0).obj (Wₙ).obj) := by
  exact ⟨deltaRootSourceGeneratorPowerReduction_isComplete_over_quotient D d b hd n,
    deltaRootSourceGeneratorPowerModP_homology_isZero D d b n hn hpA hd v hv,
    deltaRootSourceGeneratorPowerModPH0_flat D d b n hn hpA hd v hv⟩

include hn hpA hd v hv in
/-- 実二生成剰余の忠実性を標準mod p商の正確な作用へ移す。 -/
theorem deltaRootSourceGeneratorPowerModPH0_faithfullyFlat :
    Module.FaithfullyFlat Mₙ
      ((DerivedCategory.homologyFunctor (ModuleCat Mₙ) 0).obj (Wₙ).obj) := by
  let Q := A ⧸ Ideal.span (Set.insert (p : A) (Set.singleton (d ^ n)))
  let e := prismaticGeneratorPowerModPEquiv p d n
  let Y := (boundedAboveDerivedBaseChange
    (Ideal.Quotient.mk (Ideal.span (Set.insert (p : A) (Set.singleton (d ^ n)))))).obj X₀
  let M := (DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj Y.obj
  let := e.toRingHom.toAlgebra
  let : Module Mₙ M := Module.compHom M e.toRingHom
  let : IsScalarTower Mₙ Q M := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let eA : Mₙ ≃ₐ[Mₙ] Q := AlgEquiv.ofBijective (Algebra.ofId Mₙ Q) e.bijective
  have : Module.FaithfullyFlat Mₙ Q :=
    Module.FaithfullyFlat.of_linearEquiv Mₙ Mₙ eA.symm.toLinearEquiv
  have : Module.FaithfullyFlat Q M :=
    deltaRootSourcePowerResidueH0_faithfullyFlat D d b n hn hpA hd v hv
  have : Module.FaithfullyFlat Mₙ M := Module.FaithfullyFlat.trans Mₙ Q M
  exact Module.FaithfullyFlat.of_linearEquiv Mₙ M
    (prismaticGeneratorPowerModPHomologyIso p d n X₀ 0).toLinearEquiv

include hn hpA hd v hv in
/-- 標準mod p実還元と、その実H0の次数零対象の正規化同型。 -/
def deltaRootSourceGeneratorPowerModPSingleIso :
    Wₙ ≅ boundedAboveDerivedSingleFunctor.obj
      ((DerivedCategory.homologyFunctor (ModuleCat Mₙ) 0).obj (Wₙ).obj) := by
  have hPure := deltaRootSourceGeneratorPowerModP_homology_isZero D d b n hn hpA hd v hv
  let : (Wₙ).obj.IsGE 0 := (DerivedCategory.isGE_iff _ _).mpr
    (fun i hi => hPure i (by omega))
  let : (Wₙ).obj.IsLE 0 := (DerivedCategory.isLE_iff _ _).mpr
    (fun i hi => hPure i (by omega))
  exact ObjectProperty.isoMk _ (normalizedPureHomologyIso (Wₙ).obj 0)

end SerrePositivity.BhattScholze
