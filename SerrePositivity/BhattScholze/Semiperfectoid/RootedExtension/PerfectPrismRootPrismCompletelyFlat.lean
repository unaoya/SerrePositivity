module

public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.PerfectPrismRootPDPerfectionInputs
public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.DeltaAlgebra.PerfectPrismDeltaAlgebraPDCompletelyFlat
public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.DeltaRoot.DeltaRootPDCompletedPerfectionComparison

/-! # 既存根prism台環候補の標準係数射の完全忠実平坦性 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
section Coefficients
variable (D : DeltaStructure p A) (d : A) (b : σ → A)
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => deltaRootRelationFamily (p := p) b
local notation "Raw" => DeltaAdjoinDivision E (MvPolynomial.C d) r
local notation "F" => deltaAdjoinDivisionStructure E (MvPolynomial.C d) r
local notation "c" => algebraMap A Raw
local notation "z" => (c d)
local notation "B" => PDCompletionH0 Raw p z
local notation "G" => deltaPDCompletionStructure F z
local notation "s" => pdCompletionUnit Raw p z
local notation "j" => RingHom.comp s c
local notation "C" => DeltaPerfection G
local notation "κ" => deltaAlgebraPerfectionCoefficient G j
local notation "H" => PDCompletionH0 C p (κ d)
local notation "t" => RingHom.comp (pdCompletionUnit C p (κ d)) κ
local notation "T" => DeltaRootPrismCarrier D d b
local notation "f" => deltaRootPrismCoefficientMap D d b

/-- 既存の標準環同型は、両候補の元のA係数作用を保つ線形同型。 -/
def deltaRootPDPerfectionCandidateModuleIso :
    letI := pdCompletionCommRing Raw p z
    letI := pdCompletionCommRing C p (κ d)
    letI := deltaRootPrismCommRing D d b
    baseChangeScalarModule t ≅ baseChangeScalarModule f := by
  let := pdCompletionCommRing Raw p z
  let := pdCompletionCommRing C p (κ d)
  let := deltaRootPrismCommRing D d b
  let e : H ≃+* T := deltaRootPDCompletedPerfectionEquiv D d b
  let Mc : ModuleCat.{u} A := baseChangeScalarModule t
  let Nc : ModuleCat.{u} A := baseChangeScalarModule f
  let eA : Mc ≃ₗ[A] Nc :=
    { e.toAddEquiv with
      map_smul' := by
        intro a x
        change H at x
        change e (t a * x) = f a * e x
        rw [map_mul]
        exact congrArg (fun h => h * e x)
          (RingHom.congr_fun (deltaRootPDCompletedPerfectionEquiv_comp_coefficient D d b) a) }
  exact eA.toModuleIso
end Coefficients

section Perfect
variable (P : OrientedPrism p A) (hP : P.deltaStructure.IsPerfect) (b : σ → A)
local notation "D" => OrientedPrism.deltaStructure P
local notation "d" => OrientedPrism.generator P
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => deltaRootRelationFamily (p := p) b
local notation "Raw" => DeltaAdjoinDivision E (MvPolynomial.C d) r
local notation "F" => deltaAdjoinDivisionStructure E (MvPolynomial.C d) r
local notation "c" => algebraMap A Raw
local notation "z" => (c d)
local notation "G" => deltaPDCompletionStructure F z
local notation "s" => pdCompletionUnit Raw p z
local notation "j" => RingHom.comp s c
local notation "C" => DeltaPerfection G
local notation "κ" => deltaAlgebraPerfectionCoefficient G j
local notation "t" => RingHom.comp (pdCompletionUnit C p (κ d)) κ
local notation "f" => deltaRootPrismCoefficientMap D d b
local notation "M" => baseChangeScalarModule f
local notation "I" => Ideal.span {(p : A), d}
local notation "Q" => A ⧸ I
local notation "q" => Ideal.Quotient.mk I
include hP

/-- 実根PD環をδ完全化して実PD完備化した環の標準A作用は完全忠実平坦。 -/
theorem perfectPrismRootPDPerfection_isCompletelyFaithfullyFlat :
    letI := pdCompletionCommRing Raw p z
    letI := pdCompletionCommRing C p (κ d)
    IsCompletelyFaithfullyFlat I (ModuleCat.carrier (baseChangeScalarModule t)) := by
  let := pdCompletionCommRing Raw p z
  let := pdCompletionCommRing C p (κ d)
  exact perfectPrismDeltaAlgebraPD_isCompletelyFaithfullyFlat P G j hP
    (deltaRootPDSourceCoefficient_isDeltaHom D d b)
    (perfectPrismRootPDSource_reduction_homology_isZero P hP b)
    (perfectPrismRootPDSource_reductionH0_faithfullyFlat P hP b)

/-- 既存根prism台環の元の係数射は(p,d)残余Tor非輪状。 -/
theorem perfectPrismRootPrism_torVanishing :
    letI := deltaRootPrismCommRing D d b
    scalarExtensionTorVanishing q M := by
  let := pdCompletionCommRing Raw p z
  let := pdCompletionCommRing C p (κ d)
  let := deltaRootPrismCommRing D d b
  exact scalarExtensionTorVanishing_of_iso q (deltaRootPDPerfectionCandidateModuleIso D d b)
    (perfectPrismDeltaAlgebraPD_torVanishing P G j hP
      (deltaRootPDSourceCoefficient_isDeltaHom D d b)
      (perfectPrismRootPDSource_reduction_homology_isZero P hP b)
      (perfectPrismRootPDSource_reductionH0_faithfullyFlat P hP b))

/-- 同じ既存候補の通常残余係数拡大は忠実平坦。 -/
theorem perfectPrismRootPrism_scalarExtension_faithfullyFlat :
    letI := deltaRootPrismCommRing D d b
    Module.FaithfullyFlat Q ((ModuleCat.extendScalars q).obj M) := by
  let := pdCompletionCommRing Raw p z
  let := pdCompletionCommRing C p (κ d)
  let := deltaRootPrismCommRing D d b
  let M0 : ModuleCat.{u} A := baseChangeScalarModule t
  let : Module.FaithfullyFlat Q ((ModuleCat.extendScalars q).obj M0) :=
    perfectPrismDeltaAlgebraPD_scalarExtension_faithfullyFlat P G j hP
      (deltaRootPDSourceCoefficient_isDeltaHom D d b)
      (perfectPrismRootPDSource_reduction_homology_isZero P hP b)
      (perfectPrismRootPDSource_reductionH0_faithfullyFlat P hP b)
  exact Module.FaithfullyFlat.of_linearEquiv Q ((ModuleCat.extendScalars q).obj M0)
    (((ModuleCat.extendScalars q).mapIso
      (deltaRootPDPerfectionCandidateModuleIso D d b)).toLinearEquiv.symm)

/-- 任意根族の既存根prism台環候補は、その標準係数射に関して(p,d)完全忠実平坦。 -/
theorem perfectPrismRootPrism_isCompletelyFaithfullyFlat :
    letI := deltaRootPrismCommRing D d b
    IsCompletelyFaithfullyFlat I (ModuleCat.carrier M) := by
  let := deltaRootPrismCommRing D d b
  let Mc : ModuleCat.{u} A := M
  have hf : Module.FaithfullyFlat Q ((ModuleCat.extendScalars q).obj Mc) :=
    perfectPrismRootPrism_scalarExtension_faithfullyFlat P hP b
  refine ⟨isCompletelyFlat_of_acyclic_flat_reduction I Mc
    (perfectPrismRootPrism_torVanishing P hP b) hf.1, ?_⟩
  let e := (quotientScalarExtensionEquiv I Mc).trans (quotientTensorReductionEquiv I Mc).symm
  let := hf
  exact Module.FaithfullyFlat.of_linearEquiv _ _ e.symm
end Perfect
end SerrePositivity.BhattScholze
