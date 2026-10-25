module

public import SerrePositivity.BhattScholze.RootedExtension.DeltaRoot.DeltaRootBoundedSupportIteratedResidue
public import SerrePositivity.BhattScholze.Prism.PrismaticPowerDerivedFlat
public import SerrePositivity.BhattScholze.Prism.PrismaticGeneratorPowerModP
public import SerrePositivity.BhattScholze.RootedExtension.DeltaRoot.DeltaRootSourceGeneratorPowerComplete
public import SerrePositivity.BhattScholze.Prism.PerfectOrientedPrism
public import SerrePositivity.BhattScholze.Delta.DistinguishedPowerTorsion
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.DerivedPowerCokernelModel

/-! # 完全prism上の任意根族の実冪商に対するG9標準入力 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect) (b : σ → A)
local notation "D" => OrientedPrism.deltaStructure P
local notation "d" => OrientedPrism.generator P
local notation "B₀" => MvPolynomial σ A
local notation "L₀" => RelativeFreeDeltaRing (R := B₀) σ
local notation "E₀" => polynomialRankOneDeltaStructure σ D
local notation "r₀" => deltaRootRelationFamily (p := p) b
local notation "I₀" => Ideal.span {(p : L₀), MvPolynomial.C (MvPolynomial.C d)}
local notation "ψ₀" => RingHom.comp (Ideal.Quotient.mk I₀)
  (deltaDivisionSourceMap (σ := σ) E₀ (MvPolynomial.C d))
variable (n : ℕ) (hn : 0 < n)
local notation "X" => DeltaRootSourceIteratedPDCompletion D d b
local notation "Qₙ" => A ⧸ Ideal.span {(p : A), d ^ n}
local notation "Yₙ" => CategoryTheory.Functor.obj
  (boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {(p : A), d ^ n}))) X
local notation "Tₙ" => A ⧸ Ideal.span (Set.singleton (d ^ n))
local notation "Mₙ" => Tₙ ⧸ Ideal.span (Set.singleton (p : Tₙ))
local notation "Zₙ" => CategoryTheory.Functor.obj
  (boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span (Set.singleton (d ^ n))))) X
local notation "Wₙ" => CategoryTheory.Functor.obj
  (boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span (Set.singleton (p : Tₙ))))) Zₙ
include hP hn

/-- 完全prismと任意根族の実逐次源について、G10が実冪剰余の純粋性とH0忠実平坦性を与える。 -/
theorem perfectPrismRootBoundedSupportPower_pure_faithfullyFlat
    (hpres : ∀ i : ℕ, PreservesColimit
  (deltaDivisionBoundedSupportModuleDiagram E₀ r₀)
  ((ModuleCat.extendScalars.{u, u, u} ψ₀).leftDerived (i + 1))) :
    (Yₙ).obj.IsGE 0 ∧ (Yₙ).obj.IsLE 0 ∧
      Module.FaithfullyFlat Qₙ
        ((DerivedCategory.homologyFunctor (ModuleCat Qₙ) 0).obj (Yₙ).obj) := by
  obtain ⟨v, hv⟩ := P.isDistinguished_of_perfect hP
  exact prismaticPowerDerivedReduction_pure_faithfullyFlat (p : A) d n hn X
    (deltaRootBoundedSupportIteratedPDResidue_homology_isZero D d b hP.p_mul_injective
      P.generator_regular v hv hpres)
    (deltaRootBoundedSupportIteratedPDResidueH0_faithfullyFlat D d b hP.p_mul_injective
      P.generator_regular v hv hpres)

/-- 同じ生成元冪商上の標準mod p実還元は、次数零集中・H0平坦。 -/
theorem perfectPrismRootBoundedSupportPower_modP_inputs
    (hpres : ∀ i : ℕ, PreservesColimit
  (deltaDivisionBoundedSupportModuleDiagram E₀ r₀)
  ((ModuleCat.extendScalars.{u, u, u} ψ₀).leftDerived (i + 1))) :
    (∀ i : ℤ, i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat Mₙ) i).obj (Wₙ).obj)) ∧
      Module.Flat Mₙ ((DerivedCategory.homologyFunctor (ModuleCat Mₙ) 0).obj (Wₙ).obj) := by
  obtain ⟨hGE, hLE, hFF⟩ :=
    perfectPrismRootBoundedSupportPower_pure_faithfullyFlat P hP b n hn hpres
  refine ⟨?_, prismaticGeneratorPowerModPH0_flat p d n X hFF.1⟩
  intro i hi
  apply prismaticGeneratorPowerModP_homology_isZero p d n X i
  rcases lt_or_gt_of_ne hi with h | h
  · exact (DerivedCategory.isGE_iff _ _).mp hGE i h
  · exact (DerivedCategory.isLE_iff _ _).mp hLE i h

/-- 同じ具体的実冪商に、G9の完備性・係数ねじれ上界・標準mod p純粋平坦性を供給する。 -/
theorem perfectPrismRootBoundedSupportPower_G9_inputs
    (hpres : ∀ i : ℕ, PreservesColimit
  (deltaDivisionBoundedSupportModuleDiagram E₀ r₀)
  ((ModuleCat.extendScalars.{u, u, u} ψ₀).leftDerived (i + 1))) :
    DerivedCompletion.IsComplete Tₙ (p : Tₙ) (Zₙ).obj ∧
      (∀ k : ℕ, ∀ x : Tₙ, (p : Tₙ) ^ k * x = 0 → (p : Tₙ) ^ n * x = 0) ∧
      (∀ i : ℤ, i ≠ 0 →
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat Mₙ) i).obj (Wₙ).obj)) ∧
      Module.Flat Mₙ ((DerivedCategory.homologyFunctor (ModuleCat Mₙ) 0).obj (Wₙ).obj) := by
  obtain ⟨hz, hflat⟩ := perfectPrismRootBoundedSupportPower_modP_inputs P hP b n hn hpres
  refine ⟨deltaRootSourceGeneratorPowerReduction_isComplete_over_quotient
    D d b P.generator_regular n, ?_, hz, hflat⟩
  let := P.isAdicComplete_p_of_perfect hP
  intro k x hx
  exact hP.distinguished_quotient_power_p_pow_torsion_killed_by_p_pow
    (P.isDistinguished_of_perfect hP) n k x hx

/-- G9-4の同じ選択モデルのp余核複体にも、標準実還元の非零次数消滅を渡す。 -/
theorem perfectPrismRootBoundedSupportPower_modP_cokernel_homology_isZero
    (hpres : ∀ i : ℕ, PreservesColimit
  (deltaDivisionBoundedSupportModuleDiagram E₀ r₀)
  ((ModuleCat.extendScalars.{u, u, u} ψ₀).leftDerived (i + 1)))
    (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCompletion.powerCokernelComplex (p : Tₙ)
      (boundedAboveDerivedChosenModel Zₙ).complex 1).homology i) := by
  apply DerivedCompletion.powerCokernel_homology_isZero_of_reduction (p : Tₙ) 1 Zₙ i
  let H (a : Tₙ) := IsZero
    ((DerivedCategory.homologyFunctor (ModuleCat (Tₙ ⧸ Ideal.span {a})) i).obj
      ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {a}))).obj Zₙ).obj)
  have hz : H (p : Tₙ) :=
    (perfectPrismRootBoundedSupportPower_modP_inputs P hP b n hn hpres).1 i hi
  exact Eq.mp (congrArg H (_root_.pow_one (p : Tₙ)).symm) hz

end SerrePositivity.BhattScholze
