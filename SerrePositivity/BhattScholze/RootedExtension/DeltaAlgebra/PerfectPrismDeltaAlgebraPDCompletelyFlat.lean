module

public import SerrePositivity.BhattScholze.RootedExtension.DeltaAlgebra.PerfectPrismDeltaAlgebraDiscrete
public import SerrePositivity.BhattScholze.RootedExtension.DeltaAlgebra.DeltaAlgebraPerfectionPDH0Comparison
public import SerrePositivity.CommutativeAlgebra.CompletelyFlatCriterion

/-! # 実δ完全化後のPD環の完全忠実平坦性 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.DerivedCompletion
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]
variable (P : OrientedPrism p A) (E : DeltaStructure p B) (j : A →+* B)
variable (hP : P.deltaStructure.IsPerfect) (hj : P.deltaStructure.IsDeltaHom E j)
variable
    (hzero : ∀ i : ℤ, i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor
        (ModuleCat (A ⧸ Ideal.span {(p : A), P.generator})) i).obj
          ((boundedAboveDerivedBaseChange
            (Ideal.Quotient.mk (Ideal.span {(p : A), P.generator}))).obj
              (boundedAboveDerivedSingleFunctor.obj (baseChangeScalarModule j))).obj))
    (hFF : Module.FaithfullyFlat (A ⧸ Ideal.span {(p : A), P.generator})
      ((DerivedCategory.homologyFunctor
        (ModuleCat (A ⧸ Ideal.span {(p : A), P.generator})) 0).obj
          ((boundedAboveDerivedBaseChange
            (Ideal.Quotient.mk (Ideal.span {(p : A), P.generator}))).obj
              (boundedAboveDerivedSingleFunctor.obj (baseChangeScalarModule j))).obj))
local notation "d" => OrientedPrism.generator P
local notation "C" => DeltaPerfection E
local notation "κ" => deltaAlgebraPerfectionCoefficient E j
local notation "H" => PDCompletionH0 C p (κ d)
local notation "s" => pdCompletionUnit C p (κ d)
local notation "t" => RingHom.comp s κ
local notation "M" => baseChangeScalarModule t
local notation "I" => Ideal.span {(p : A), d}
local notation "Q" => A ⧸ I
local notation "q" => Ideal.Quotient.mk I
local notation "X" => DeltaAlgebraPerfectionIteratedPDCompletion E j d
local notation "Y" => CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange q)
  (Functor.obj boundedAboveDerivedSingleFunctor M)
include hP hj hzero hFF

/-- 同じ実δ完全化逐次対象は、元の標準係数射を持つ実PD環のsingleと同型。 -/
def perfectPrismDeltaAlgebraPDSingleIso :
    letI := pdCompletionCommRing C p (κ d)
    X ≅ boundedAboveDerivedSingleFunctor.obj M := by
  let := pdCompletionCommRing C p (κ d)
  exact ObjectProperty.isoMk _
    (perfectPrismDeltaAlgebraCompletionSingleIso P E j hP hj hzero hFF ≪≫
      (DerivedCategory.singleFunctor (ModuleCat A) 0).mapIso
        (deltaAlgebraPerfectionPDH0Iso E j d))

/-- 同じ標準PD係数作用での(p,d)実還元の非零次数は零。 -/
theorem perfectPrismDeltaAlgebraPD_reduction_homology_isZero (i : ℤ) (hi : i ≠ 0) :
    letI := pdCompletionCommRing C p (κ d)
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q) i).obj (Y).obj) := by
  let := pdCompletionCommRing C p (κ d)
  obtain ⟨_, _, hz, _⟩ :=
    perfectPrismDeltaAlgebraCompletion_residue_inputs E j P hP hj hzero hFF
  exact (hz i hi).of_iso ((DerivedCategory.homologyFunctor (ModuleCat Q) i).mapIso
    (DerivedCategory.Minus.ι.mapIso ((boundedAboveDerivedBaseChange q).mapIso
      (perfectPrismDeltaAlgebraPDSingleIso P E j hP hj hzero hFF)))).symm

/-- 同じ標準PD係数作用での実還元H0は忠実平坦。 -/
theorem perfectPrismDeltaAlgebraPD_reductionH0_faithfullyFlat :
    letI := pdCompletionCommRing C p (κ d)
    Module.FaithfullyFlat Q ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj (Y).obj) := by
  let := pdCompletionCommRing C p (κ d)
  obtain ⟨_, _, _, hf⟩ :=
    perfectPrismDeltaAlgebraCompletion_residue_inputs E j P hP hj hzero hFF
  let : Module.FaithfullyFlat Q ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj
      ((boundedAboveDerivedBaseChange q).obj X).obj) := hf
  exact Module.FaithfullyFlat.of_linearEquiv Q
    ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj
      ((boundedAboveDerivedBaseChange q).obj X).obj)
    ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).mapIso
      (DerivedCategory.Minus.ι.mapIso ((boundedAboveDerivedBaseChange q).mapIso
        (perfectPrismDeltaAlgebraPDSingleIso P E j hP hj hzero hFF)))).toLinearEquiv.symm

/-- 同じ標準PD係数加群は、元の(p,d)係数拡大に関してTor非輪状。 -/
theorem perfectPrismDeltaAlgebraPD_torVanishing :
    letI := pdCompletionCommRing C p (κ d)
    scalarExtensionTorVanishing q M := by
  let := pdCompletionCommRing C p (κ d)
  apply (derivedModuleBaseChange_negative_homology_vanishes_iff q M).mp
  intro n hn
  exact (perfectPrismDeltaAlgebraPD_reduction_homology_isZero
    P E j hP hj hzero hFF (-(n : ℤ)) (by omega)).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat Q) (-(n : ℤ))).mapIso
      ((boundedAboveDerivedBaseChangeModuleNatIso q).app M)).symm

/-- 同じPD係数加群の通常剰余係数拡大は忠実平坦。 -/
theorem perfectPrismDeltaAlgebraPD_scalarExtension_faithfullyFlat :
    letI := pdCompletionCommRing C p (κ d)
    Module.FaithfullyFlat Q ((ModuleCat.extendScalars q).obj M) := by
  let := pdCompletionCommRing C p (κ d)
  let : Module.FaithfullyFlat Q
      ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj (Y).obj) :=
    perfectPrismDeltaAlgebraPD_reductionH0_faithfullyFlat P E j hP hj hzero hFF
  exact Module.FaithfullyFlat.of_linearEquiv Q
    ((DerivedCategory.homologyFunctor (ModuleCat Q) 0).obj (Y).obj)
    ((boundedAboveDerivedBaseChangeModuleH0Iso q).app M).toLinearEquiv.symm

/-- 実δ完全化後のPD環は、その標準A係数作用で(p,d)完全忠実平坦。 -/
theorem perfectPrismDeltaAlgebraPD_isCompletelyFaithfullyFlat :
    letI := pdCompletionCommRing C p (κ d)
    IsCompletelyFaithfullyFlat I (ModuleCat.carrier M) := by
  let := pdCompletionCommRing C p (κ d)
  let Mc : ModuleCat.{u} A := M
  have hf : Module.FaithfullyFlat Q ((ModuleCat.extendScalars q).obj Mc) :=
    perfectPrismDeltaAlgebraPD_scalarExtension_faithfullyFlat P E j hP hj hzero hFF
  refine ⟨isCompletelyFlat_of_acyclic_flat_reduction I Mc
    (perfectPrismDeltaAlgebraPD_torVanishing P E j hP hj hzero hFF) hf.1, ?_⟩
  let e := (quotientScalarExtensionEquiv I Mc).trans (quotientTensorReductionEquiv I Mc).symm
  let := hf
  exact Module.FaithfullyFlat.of_linearEquiv _ _ e.symm

end SerrePositivity.BhattScholze
