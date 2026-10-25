module

public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.Division.DeltaDivisionBoundedSupportTor
public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.DeltaRoot.DeltaRootSourceCoefficientResidue

/-! # 任意根族の全源Tor入力から元の実係数還元への比較 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (b : σ → A)
local notation "P" => MvPolynomial σ A
local notation "L" => RelativeFreeDeltaRing (R := P) σ
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => deltaRootRelationFamily (p := p) b
local notation "I" => Ideal.span {(p : L), MvPolynomial.C (MvPolynomial.C d)}
local notation "Q" => L ⧸ I
local notation "ψ" => RingHom.comp (Ideal.Quotient.mk I)
  (deltaDivisionSourceMap (σ := σ) E (MvPolynomial.C d))
local notation "β" => deltaDivisionSourceEval E r
local notation "Mψ" => baseChangeScalarModule ψ
local notation "Mβ" => baseChangeScalarModule β
local notation "F" => deltaDivisionBoundedSupportModuleDiagram E r
local notation "Res" => DeltaAdjoinDivisionResidue E (MvPolynomial.C d) r
local notation "MRes" => CategoryTheory.Functor.obj
  (ModuleCat.restrictScalars β) (ModuleCat.of P Res)

/-- 有界深さ図式のTor交換入力により、任意根族の実β拡大の高次Torは零。 -/
theorem deltaRootBoundedSupportResidueEval_torVanishing
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d) (hpres : ∀ i : ℕ, PreservesColimit F
      ((ModuleCat.extendScalars.{u, u, u} ψ).leftDerived (i + 1))) :
    scalarExtensionTorVanishing β Mψ := by
  intro n hn
  cases n with
  | zero => exact (Nat.lt_irrefl 0 hn).elim
  | succ i =>
    let := deltaDivisionSourceEvaluationAlgebra E r
    let : Subsingleton (((ModuleCat.extendScalars ψ).leftDerived (i + 1)).obj Mβ) :=
      deltaRootEvaluation_tor_subsingleton_of_preservesBoundedSupportColimit
        D d b hpA v hv i (hpres i)
    have hz : IsZero (((ModuleCat.extendScalars ψ).leftDerived (i + 1)).obj Mβ) :=
      ModuleCat.isZero_of_subsingleton _
    have hH := (derivedModuleBaseChangeHomologyIso ψ (i + 1)).app Mβ
    have hzH := hH.isZero_iff.mpr hz
    have hzR := (ModuleCat.restrictScalars ψ).map_isZero hzH
    have hzT := ((derivedModuleBaseChangeTorIso ψ (i + 1)).app Mβ).isZero_iff.mp hzR
    exact ((torComm (i + 1) Mβ Mψ).toModuleIso).isZero_iff.mpr hzT

/-- 同じ実β導来拡大は、既存raw残余商の次数零対象と標準augmentationで比較される。 -/
def deltaRootBoundedSupportResidueDerivedIso
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d) (hpres : ∀ i : ℕ, PreservesColimit F
      ((ModuleCat.extendScalars.{u, u, u} ψ).leftDerived (i + 1))) :
    (boundedAboveDerivedBaseChange β).obj (boundedAboveDerivedSingleFunctor.obj Mψ) ≅
      boundedAboveDerivedSingleFunctor.obj (ModuleCat.of P Res) := by
  letI := deltaDivisionSourceEvaluationAlgebra E r
  letI := deltaDivisionSourceResidueTargetAlgebra (σ := σ) E (MvPolynomial.C d)
  letI : Module L Q := Algebra.toModule
  let e := (deltaRootResidueSourceEvalScalarEquiv D d b).trans
    (deltaDivisionSourceResidueTensorAlgEquiv E (MvPolynomial.C d) r).toLinearEquiv
  exact boundedAboveDerivedBaseChangeModuleAugmentationIso β Mψ
    (deltaRootBoundedSupportResidueEval_torVanishing D d b hpA v hv hpres) ≪≫
      boundedAboveDerivedSingleFunctor.mapIso e.toModuleIso

/-- 比較の順射は、元の標準導来augmentationと通常raw残余比較の合成そのもの。 -/
theorem deltaRootBoundedSupportResidueDerivedIso_hom
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d) (hpres : ∀ i : ℕ, PreservesColimit F
      ((ModuleCat.extendScalars.{u, u, u} ψ).leftDerived (i + 1))) :
    letI := deltaDivisionSourceEvaluationAlgebra E r
    letI := deltaDivisionSourceResidueTargetAlgebra (σ := σ) E (MvPolynomial.C d)
    letI : Module L Q := Algebra.toModule
    let e := (deltaRootResidueSourceEvalScalarEquiv D d b).trans
      (deltaDivisionSourceResidueTensorAlgEquiv E (MvPolynomial.C d) r).toLinearEquiv
    (deltaRootBoundedSupportResidueDerivedIso D d b hpA v hv hpres).hom.hom =
      (boundedAboveDerivedBaseChangeModuleAugmentation β).app Mψ ≫
        (boundedAboveDerivedSingleFunctor.map e.toModuleIso.hom).hom := by
  rfl

/-- 元の任意根族の実三因子係数還元は、同じraw残余商のsingleと標準同型。 -/
def deltaRootBoundedSupportCoefficientResidueIso
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d) (hpres : ∀ i : ℕ, PreservesColimit F
      ((ModuleCat.extendScalars.{u, u, u} ψ).leftDerived (i + 1))) :
    DeltaRootSourceCoefficientReduced D d b ≅ boundedAboveDerivedSingleFunctor.obj MRes := by
  let e₁ := deltaDivisionSourceResidueAssociatorReductionIso E (MvPolynomial.C d) r
  let e₂ := (boundedAboveDerivedBaseChangeTensorIso β
    (boundedAboveDerivedSingleFunctor.obj Mψ)).symm
  let e₃ := (boundedAboveDerivedRestrictScalars β).mapIso
    (deltaRootBoundedSupportResidueDerivedIso D d b hpA v hv hpres)
  let e₄ : (boundedAboveDerivedRestrictScalars β).obj
      (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of P Res)) ≅
        boundedAboveDerivedSingleFunctor.obj MRes :=
    ObjectProperty.isoMk _
      ((derivedRestrictScalarsSingleIso β 0).app (ModuleCat.of P Res))
  exact e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄

/-- 同じ実三因子係数還元のH0は、βによる源作用を持つraw残余商と同型。 -/
def deltaRootBoundedSupportCoefficientResidueH0Iso
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d) (hpres : ∀ i : ℕ, PreservesColimit F
      ((ModuleCat.extendScalars.{u, u, u} ψ).leftDerived (i + 1))) :
    ((DerivedCategory.homologyFunctor (ModuleCat L) 0).obj
      (DeltaRootSourceCoefficientReduced D d b).obj) ≅ MRes :=
  ((DerivedCategory.homologyFunctor (ModuleCat L) 0).mapIso
    (DerivedCategory.Minus.ι.mapIso
      (deltaRootBoundedSupportCoefficientResidueIso D d b hpA v hv hpres))) ≪≫
        (realizedSingleH0Iso L).app MRes

/-- 同じ実三因子係数還元は、非零次数のホモロジーがすべて零。 -/
theorem deltaRootBoundedSupportCoefficientResidue_homology_isZero
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d) (hpres : ∀ i : ℕ, PreservesColimit F
      ((ModuleCat.extendScalars.{u, u, u} ψ).leftDerived (i + 1))) (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat L) i).obj
      (DeltaRootSourceCoefficientReduced D d b).obj) :=
  (derivedSingleHomology_isZero MRes i hi).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat L) i).mapIso
      (DerivedCategory.Minus.ι.mapIso
        (deltaRootBoundedSupportCoefficientResidueIso D d b hpA v hv hpres)))

end SerrePositivity.BhattScholze
