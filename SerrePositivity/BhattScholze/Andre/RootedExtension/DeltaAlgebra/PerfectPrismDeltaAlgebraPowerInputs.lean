module

public import SerrePositivity.BhattScholze.Andre.RootedExtension.DeltaAlgebra.DeltaAlgebraPerfectionPowerComplete
public import SerrePositivity.BhattScholze.Prism.Residue.PrismaticResidue
public import SerrePositivity.BhattScholze.Delta.Perfect.DistinguishedRegular
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.DerivedPowerCokernelModel

/-! # 実δ完全化逐次対象の生成元冪商上のG9入力 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable (P : OrientedPrism p A) (E : DeltaStructure p B) (j : A →+* B) (n : ℕ)
local notation "d" => OrientedPrism.generator P
local notation "Q₀" => A ⧸ Ideal.span {(p : A), d}
local notation "X₀" => CategoryTheory.Functor.obj boundedAboveDerivedSingleFunctor
  (baseChangeScalarModule j)
local notation "Y₀" => CategoryTheory.Functor.obj
  (boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {(p : A), d}))) X₀
local notation "X" => DeltaAlgebraPerfectionIteratedPDCompletion E j d
local notation "Tₙ" => A ⧸ Ideal.span (Set.singleton (d ^ n))
local notation "Mₙ" => Tₙ ⧸ Ideal.span (Set.singleton (p : Tₙ))
local notation "Zₙ" => CategoryTheory.Functor.obj
  (boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span (Set.singleton (d ^ n))))) X
local notation "Wₙ" => CategoryTheory.Functor.obj
  (boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span (Set.singleton (p : Tₙ))))) Zₙ

/-- G10と標準商比較により、同じ生成元冪商上のmod p還元は次数零・H0平坦。 -/
theorem perfectPrismDeltaAlgebraCompletionPower_modP_inputs
    (hP : P.deltaStructure.IsPerfect) (hj : P.deltaStructure.IsDeltaHom E j)
    (hzero : ∀ i : ℤ, i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q₀) i).obj (Y₀).obj))
    (hFF : Module.FaithfullyFlat Q₀
      ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj (Y₀).obj)) (hn : 0 < n) :
    (∀ i : ℤ, i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat Mₙ) i).obj (Wₙ).obj)) ∧
      Module.Flat Mₙ ((DerivedCategory.homologyFunctor (ModuleCat Mₙ) 0).obj (Wₙ).obj) := by
  obtain ⟨_, _, hz, hff⟩ :=
    perfectPrismDeltaAlgebraCompletion_residue_inputs E j P hP hj hzero hFF
  obtain ⟨hGE, hLE, hFlat⟩ :=
    prismaticPowerDerivedReduction_pure_faithfullyFlat (p : A) d n hn X hz hff
  refine ⟨?_, prismaticGeneratorPowerModPH0_flat p d n X hFlat.1⟩
  intro i hi
  apply prismaticGeneratorPowerModP_homology_isZero p d n X i
  rcases lt_or_gt_of_ne hi with h | h
  · exact (DerivedCategory.isGE_iff _ _).mp hGE i h
  · exact (DerivedCategory.isLE_iff _ _).mp hLE i h

/-- 同じ実冪商対象について、完備性・係数ねじれ上界・標準mod p入力を供給する。 -/
theorem perfectPrismDeltaAlgebraCompletionPower_G9_inputs
    (hP : P.deltaStructure.IsPerfect) (hj : P.deltaStructure.IsDeltaHom E j)
    (hzero : ∀ i : ℤ, i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q₀) i).obj (Y₀).obj))
    (hFF : Module.FaithfullyFlat Q₀
      ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj (Y₀).obj)) (hn : 0 < n) :
    DerivedCompletion.IsComplete Tₙ (p : Tₙ) (Zₙ).obj ∧
      (∀ k : ℕ, ∀ x : Tₙ, (p : Tₙ) ^ k * x = 0 → (p : Tₙ) ^ n * x = 0) ∧
      (∀ i : ℤ, i ≠ 0 →
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat Mₙ) i).obj (Wₙ).obj)) ∧
      Module.Flat Mₙ ((DerivedCategory.homologyFunctor (ModuleCat Mₙ) 0).obj (Wₙ).obj) := by
  obtain ⟨hz, hflat⟩ :=
    perfectPrismDeltaAlgebraCompletionPower_modP_inputs P E j n hP hj hzero hFF hn
  refine ⟨deltaAlgebraPerfectionGeneratorPowerReduction_isComplete_over_quotient
    E j d P.generator_regular n, ?_, hz, hflat⟩
  let := P.isAdicComplete_p_of_perfect hP
  intro k x hx
  exact hP.distinguished_quotient_power_p_pow_torsion_killed_by_p_pow
    (P.isDistinguished_of_perfect hP) n k x hx

/-- G9-4の元の選択モデルのp余核複体へ、同じ実標準還元の消滅を渡す。 -/
theorem perfectPrismDeltaAlgebraCompletionPower_modP_cokernel_homology_isZero
    (hP : P.deltaStructure.IsPerfect) (hj : P.deltaStructure.IsDeltaHom E j)
    (hzero : ∀ i : ℤ, i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q₀) i).obj (Y₀).obj))
    (hFF : Module.FaithfullyFlat Q₀
      ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj (Y₀).obj)) (hn : 0 < n)
    (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCompletion.powerCokernelComplex (p : Tₙ)
      (boundedAboveDerivedChosenModel Zₙ).complex 1).homology i) := by
  apply DerivedCompletion.powerCokernel_homology_isZero_of_reduction (p : Tₙ) 1 Zₙ i
  let H (a : Tₙ) := IsZero
    ((DerivedCategory.homologyFunctor (ModuleCat (Tₙ ⧸ Ideal.span {a})) i).obj
      ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {a}))).obj Zₙ).obj)
  have hz : H (p : Tₙ) :=
    (perfectPrismDeltaAlgebraCompletionPower_modP_inputs P E j n hP hj hzero hFF hn).1 i hi
  exact Eq.mp (congrArg H (_root_.pow_one (p : Tₙ)).symm) hz

end SerrePositivity.BhattScholze
