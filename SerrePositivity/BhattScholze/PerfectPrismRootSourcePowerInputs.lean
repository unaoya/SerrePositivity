module

public import SerrePositivity.BhattScholze.DeltaRootSourceGeneratorPowerModPFlat
public import SerrePositivity.BhattScholze.PerfectOrientedPrism
public import SerrePositivity.BhattScholze.DistinguishedPowerTorsion
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.DerivedPowerCokernelModel

/-! # 完全prismによる元のr/d実対象のG9入力の供給 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect) (b : σ → A)
local notation "D" => OrientedPrism.deltaStructure P
local notation "d" => OrientedPrism.generator P
include hP

private theorem sourceGeneratorRegular : IsSMulRegular A d := by
  let := P.isAdicComplete_p_of_perfect hP
  exact hP.distinguished_mul_injective (P.isDistinguished_of_perfect hP)

variable (n : ℕ) (hn : 0 < n)
local notation "Tₙ" => A ⧸ Ideal.span (Set.singleton (d ^ n))
local notation "Mₙ" => Tₙ ⧸ Ideal.span (Set.singleton (p : Tₙ))
local notation "X" => DeltaRootSourceIteratedPDCompletion D d b
local notation "Zₙ" => CategoryTheory.Functor.obj
  (boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span (Set.singleton (d ^ n))))) X
local notation "Wₙ" => CategoryTheory.Functor.obj
  (boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span (Set.singleton (p : Tₙ))))) Zₙ
include hn

/-- 完全prismだけから、元の生成元冪商上の標準mod p実還元の次数消滅を得る。 -/
theorem perfectPrismRootSourcePower_modP_homology_isZero (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat Mₙ) i).obj (Wₙ).obj) := by
  obtain ⟨v, hv⟩ := P.isDistinguished_of_perfect hP
  exact deltaRootSourceGeneratorPowerModP_homology_isZero D d b n hn hP.p_mul_injective
    (sourceGeneratorRegular P hP) v hv i hi

/-- 元の実標準mod p還元H0の忠実平坦性。追加単元・ghost仮定は不要。 -/
theorem perfectPrismRootSourcePower_modPH0_faithfullyFlat :
    Module.FaithfullyFlat Mₙ ((DerivedCategory.homologyFunctor (ModuleCat Mₙ) 0).obj (Wₙ).obj) := by
  obtain ⟨v, hv⟩ := P.isDistinguished_of_perfect hP
  exact deltaRootSourceGeneratorPowerModPH0_faithfullyFlat D d b n hn hP.p_mul_injective
    (sourceGeneratorRegular P hP) v hv

/-- 完備性・係数環のpⁿねじれ上界・実標準mod p還元を、同じ具体的対象で供給する。 -/
theorem perfectPrismRootSourcePower_G9_inputs :
    DerivedCompletion.IsComplete Tₙ (p : Tₙ) (Zₙ).obj ∧
      (∀ k : ℕ, ∀ x : Tₙ, (p : Tₙ) ^ k * x = 0 → (p : Tₙ) ^ n * x = 0) ∧
      (∀ i : ℤ, i ≠ 0 →
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat Mₙ) i).obj (Wₙ).obj)) ∧
      Module.FaithfullyFlat Mₙ
        ((DerivedCategory.homologyFunctor (ModuleCat Mₙ) 0).obj (Wₙ).obj) := by
  refine ⟨deltaRootSourceGeneratorPowerReduction_isComplete_over_quotient D d b
      (sourceGeneratorRegular P hP) n, ?_,
    perfectPrismRootSourcePower_modP_homology_isZero P hP b n hn,
    perfectPrismRootSourcePower_modPH0_faithfullyFlat P hP b n hn⟩
  let := P.isAdicComplete_p_of_perfect hP
  intro k x hx
  exact hP.distinguished_quotient_power_p_pow_torsion_killed_by_p_pow
    (P.isDistinguished_of_perfect hP) n k x hx

/-- G9-4の比較で、元の実Tₙ対象の選択射影モデルのp余核複体へ次数消滅を渡す。 -/
theorem perfectPrismRootSourcePower_modP_cokernel_homology_isZero (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCompletion.powerCokernelComplex (p : Tₙ)
      (boundedAboveDerivedChosenModel Zₙ).complex 1).homology i) := by
  apply DerivedCompletion.powerCokernel_homology_isZero_of_reduction (p : Tₙ) 1 Zₙ i
  let H (a : Tₙ) := IsZero
    ((DerivedCategory.homologyFunctor (ModuleCat (Tₙ ⧸ Ideal.span {a})) i).obj
      ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {a}))).obj Zₙ).obj)
  have hz : H (p : Tₙ) :=
    perfectPrismRootSourcePower_modP_homology_isZero P hP b n hn i hi
  exact Eq.mp (congrArg H (_root_.pow_one (p : Tₙ)).symm) hz

end SerrePositivity.BhattScholze
