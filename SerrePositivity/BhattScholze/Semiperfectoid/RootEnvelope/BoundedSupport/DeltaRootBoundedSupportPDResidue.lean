module

public import SerrePositivity.BhattScholze.Andre.RootedExtension.DeltaRoot.DeltaRootSourcePDReduction
public import SerrePositivity.BhattScholze.Semiperfectoid.RootEnvelope.BoundedSupport.DeltaRootBoundedSupportQuotientFlat

/-! # 元の係数環上の実(p,d)還元とraw残余商

任意根族（明示したTor交換入力の下）の実源商での比較を元の係数環へ渡す。一般Koszul還元や完備化後CFFは含まない。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (b : σ → A)
local notation "P₀" => MvPolynomial σ A
local notation "L₀" => RelativeFreeDeltaRing (R := P₀) σ
local notation "E₀" => polynomialRankOneDeltaStructure σ D
local notation "c₀" => deltaRootRelationFamily (p := p) b
local notation "K₀" => Ideal.span {(p : L₀), MvPolynomial.C (MvPolynomial.C d)}
local notation "Q₀" => L₀ ⧸ K₀
local notation "I₀" => Ideal.span {(p : A), d}
local notation "R₀" => A ⧸ I₀
local notation "κ₀" => deltaRootSourceQuotientCoefficientMap (σ := σ) (p := p) d
local notation "α₀" => deltaDivisionSourceMap (σ := σ) E₀ (MvPolynomial.C d)
local notation "ψ₀" => RingHom.comp (Ideal.Quotient.mk K₀) α₀
local notation "Res₀" => DeltaAdjoinDivisionResidue E₀ (MvPolynomial.C d) c₀
local notation "Y₀" => CategoryTheory.Functor.obj
  (boundedAboveDerivedBaseChange (Ideal.Quotient.mk I₀)) (DeltaRootSourceCoefficientObject d D b)
local notation "MRes" => CategoryTheory.Functor.obj (ModuleCat.restrictScalars κ₀)
  (ModuleCat.of Q₀ Res₀)

/-- 元のA上の実根添加対象の実(p,d)還元と、作用を制限したraw商のsingle比較。 -/
def deltaRootBoundedSupportCoefficientPDResidueIso
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (hpres : ∀ i : ℕ, PreservesColimit
      (deltaDivisionBoundedSupportModuleDiagram E₀ c₀)
      ((ModuleCat.extendScalars.{u, u, u} ψ₀).leftDerived (i + 1))) :
    letI := (deltaRootSourceQuotientResidueMap D d b).toAlgebra
    letI : Module Q₀ Res₀ := Algebra.toModule
    Y₀ ≅ boundedAboveDerivedSingleFunctor.obj MRes := by
  letI := (deltaRootSourceQuotientResidueMap D d b).toAlgebra
  letI : Module Q₀ Res₀ := Algebra.toModule
  exact deltaRootSourceCoefficientPDReductionIso d D b ≪≫
    (boundedAboveDerivedRestrictScalars κ₀).mapIso
      (deltaRootBoundedSupportQuotientDerivedSingleIso D d b hpA v hv hpres) ≪≫
    ObjectProperty.isoMk _ ((derivedRestrictScalarsSingleIso κ₀ 0).app (ModuleCat.of Q₀ Res₀))

/-- 元のA上の実還元のH0と、標準係数作用を制限したraw商の加群同型。 -/
def deltaRootBoundedSupportCoefficientPDResidueH0Iso
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (hpres : ∀ i : ℕ, PreservesColimit
      (deltaDivisionBoundedSupportModuleDiagram E₀ c₀)
      ((ModuleCat.extendScalars.{u, u, u} ψ₀).leftDerived (i + 1))) :
    letI := (deltaRootSourceQuotientResidueMap D d b).toAlgebra
    letI : Module Q₀ Res₀ := Algebra.toModule
    (DerivedCategory.homologyFunctor (ModuleCat R₀) 0).obj (Y₀).obj ≅ MRes := by
  letI := (deltaRootSourceQuotientResidueMap D d b).toAlgebra
  letI : Module Q₀ Res₀ := Algebra.toModule
  exact (DerivedCategory.homologyFunctor (ModuleCat R₀) 0).mapIso
      (DerivedCategory.Minus.ι.mapIso
        (deltaRootBoundedSupportCoefficientPDResidueIso D d b hpA v hv hpres)) ≪≫
    (realizedSingleH0Iso R₀).app MRes

/-- 元のA上の実(p,d)還元の非零次数ホモロジーは零。 -/
theorem deltaRootBoundedSupportCoefficientPDResidue_homology_isZero
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (hpres : ∀ i : ℕ, PreservesColimit
      (deltaDivisionBoundedSupportModuleDiagram E₀ c₀)
      ((ModuleCat.extendScalars.{u, u, u} ψ₀).leftDerived (i + 1)))
    (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat R₀) i).obj (Y₀).obj) := by
  let := (deltaRootSourceQuotientResidueMap D d b).toAlgebra
  let : Module Q₀ Res₀ := Algebra.toModule
  exact (derivedSingleHomology_isZero MRes i hi).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat R₀) i).mapIso
      (DerivedCategory.Minus.ι.mapIso
        (deltaRootBoundedSupportCoefficientPDResidueIso D d b hpA v hv hpres)))

/-- 元のA上の実(p,d)還元のH0は、実係数商A/(p,d)上忠実平坦。 -/
theorem deltaRootBoundedSupportCoefficientPDResidueH0_faithfullyFlat
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (hpres : ∀ i : ℕ, PreservesColimit
      (deltaDivisionBoundedSupportModuleDiagram E₀ c₀)
      ((ModuleCat.extendScalars.{u, u, u} ψ₀).leftDerived (i + 1))) :
    Module.FaithfullyFlat R₀
      ((DerivedCategory.homologyFunctor (ModuleCat R₀) 0).obj (Y₀).obj) := by
  let e : (DerivedCategory.homologyFunctor (ModuleCat R₀) 0).obj (Y₀).obj ≅
      (ModuleCat.restrictScalars κ₀).obj
        ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj
          (DeltaRootSourceQuotientDerived D d b).obj) :=
    (DerivedCategory.homologyFunctor (ModuleCat R₀) 0).mapIso
      (DerivedCategory.Minus.ι.mapIso (deltaRootSourceCoefficientPDReductionIso d D b)) ≪≫
    (derivedRestrictScalarsHomologyIso κ₀ 0).app (DeltaRootSourceQuotientDerived D d b).obj
  have := deltaRootBoundedSupportQuotientDerivedH0_faithfullyFlat
    D d b hpA v hv hpres
  exact Module.FaithfullyFlat.of_linearEquiv _ _ e.toLinearEquiv

end SerrePositivity.BhattScholze
