module

public import SerrePositivity.BhattScholze.DeltaRootSourcePowerResidueDiscrete
public import SerrePositivity.BhattScholze.PrismaticGeneratorPowerModP
public import SerrePositivity.BhattScholze.DeltaRootSourceGeneratorPowerComplete

/-! # G9へ渡す実生成元冪商の標準mod p入力 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
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

end SerrePositivity.BhattScholze
