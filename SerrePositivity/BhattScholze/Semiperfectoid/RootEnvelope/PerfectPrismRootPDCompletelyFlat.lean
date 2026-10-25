module

public import SerrePositivity.BhattScholze.Semiperfectoid.RootEnvelope.PerfectPrismRootSourceDiscrete
public import SerrePositivity.BhattScholze.Semiperfectoid.RootEnvelope.Source.DeltaRootRawCompletedH0Ring
public import SerrePositivity.CommutativeAlgebra.CompletelyFlatCriterion

/-! # 完全prism上の任意根族の実PD完備化環の完全忠実平坦性 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.DerivedCompletion
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect) (b : σ → A)
local notation "D" => OrientedPrism.deltaStructure P
local notation "d" => OrientedPrism.generator P
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => deltaRootRelationFamily (p := p) b
local notation "Raw" => DeltaAdjoinDivision E (MvPolynomial.C d) r
local notation "c" => algebraMap A Raw
local notation "B" => PDCompletionH0 Raw p (c d)
local notation "M" => CategoryTheory.Functor.obj (ModuleCat.restrictScalars c) (ModuleCat.of Raw B)
local notation "I" => Ideal.span {(p : A), d}
local notation "Q" => A ⧸ I
local notation "q" => Ideal.Quotient.mk I
local notation "X" => DeltaRootSourceIteratedPDCompletion D d b
local notation "Y" => CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange q)
  (boundedAboveDerivedSingleFunctor.obj M)
include hP

/-- 元の実逐次源は、標準A作用付きraw PD環のsingle対象と同型。 -/
def perfectPrismRootSourcePDSingleIso : X ≅ boundedAboveDerivedSingleFunctor.obj M :=
  ObjectProperty.isoMk _ (perfectPrismRootSourceSingleIso P hP b ≪≫
    (DerivedCategory.singleFunctor (ModuleCat A) 0).mapIso (deltaRootSourcePDH0Iso D d b))

/-- 実PD環の同じ(p,d)導来還元の非零次数は消える。 -/
theorem perfectPrismRootPD_reduction_homology_isZero (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q) i).obj (Y).obj) := by
  obtain ⟨v, hv⟩ := P.isDistinguished_of_perfect hP
  have hz := deltaRootBoundedSupportIteratedPDResidue_homology_isZero D d b
    hP.p_mul_injective P.generator_regular v hv
    (deltaRootBoundedSupport_preservesColimit D d b) i hi
  exact hz.of_iso ((DerivedCategory.homologyFunctor (ModuleCat Q) i).mapIso
    (DerivedCategory.Minus.ι.mapIso
      ((boundedAboveDerivedBaseChange q).mapIso (perfectPrismRootSourcePDSingleIso P hP b)))).symm

/-- 実PD環の同じ(p,d)導来還元のH0は忠実平坦。 -/
theorem perfectPrismRootPD_reductionH0_faithfullyFlat :
    Module.FaithfullyFlat Q ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj (Y).obj) := by
  obtain ⟨v, hv⟩ := P.isDistinguished_of_perfect hP
  let : Module.FaithfullyFlat Q
      ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj
        ((boundedAboveDerivedBaseChange q).obj X).obj) :=
    deltaRootBoundedSupportIteratedPDResidueH0_faithfullyFlat D d b
    hP.p_mul_injective P.generator_regular v hv
    (deltaRootBoundedSupport_preservesColimit D d b)
  exact Module.FaithfullyFlat.of_linearEquiv Q
    ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj
      ((boundedAboveDerivedBaseChange q).obj X).obj)
    ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).mapIso
      (DerivedCategory.Minus.ι.mapIso
        ((boundedAboveDerivedBaseChange q).mapIso
          (perfectPrismRootSourcePDSingleIso P hP b)))).toLinearEquiv.symm

/-- 実PD環の具体的A係数加群の(p,d)高次Torは零。 -/
theorem perfectPrismRootPD_torVanishing : scalarExtensionTorVanishing q M := by
  apply (derivedModuleBaseChange_negative_homology_vanishes_iff q M).mp
  intro n hn
  exact (perfectPrismRootPD_reduction_homology_isZero P hP b (-(n : ℤ)) (by omega)).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat Q) (-(n : ℤ))).mapIso
      ((boundedAboveDerivedBaseChangeModuleNatIso q).app M)).symm

/-- 実PD環の通常係数拡大も同じ商環上忠実平坦。 -/
theorem perfectPrismRootPD_scalarExtension_faithfullyFlat :
    Module.FaithfullyFlat Q ((ModuleCat.extendScalars q).obj M) := by
  let : Module.FaithfullyFlat Q
      ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj (Y).obj) :=
    perfectPrismRootPD_reductionH0_faithfullyFlat P hP b
  exact Module.FaithfullyFlat.of_linearEquiv Q
    ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj (Y).obj)
    ((boundedAboveDerivedBaseChangeModuleH0Iso q).app M).toLinearEquiv.symm

/-- 任意根族のraw実PD環は、元の(p,d)に関して完全忠実平坦。 -/
theorem perfectPrismRootPD_isCompletelyFaithfullyFlat :
    IsCompletelyFaithfullyFlat I (ModuleCat.carrier M) := by
  let Mc : ModuleCat.{u} A := M
  have hFF : Module.FaithfullyFlat Q ((ModuleCat.extendScalars q).obj Mc) :=
    perfectPrismRootPD_scalarExtension_faithfullyFlat P hP b
  refine ⟨isCompletelyFlat_of_acyclic_flat_reduction I Mc
    (perfectPrismRootPD_torVanishing P hP b) hFF.1, ?_⟩
  let e := (quotientScalarExtensionEquiv I Mc).trans (quotientTensorReductionEquiv I Mc).symm
  let := hFF
  exact Module.FaithfullyFlat.of_linearEquiv _ _ e.symm

end SerrePositivity.BhattScholze
