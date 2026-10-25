module

public import SerrePositivity.BhattScholze.RootedExtension.DeltaRoot.DeltaRootSourcePowerResidue
public import SerrePositivity.BhattScholze.Prism.PrismaticPowerResidueCanonical

/-! # 具体的根添加対象のG10標準冪零還元入力

標準商環上での次数零集中とH0忠実平坦性を供給する。
冪零厚化前の対象の離散性・平坦性はG10の別工程である。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (D : DeltaStructure p A) (d : A) (b : σ → A) (n : ℕ) (hn : 0 < n)
local notation "P₀" => MvPolynomial σ A
local notation "L₀" => RelativeFreeDeltaRing (R := P₀) σ
local notation "E₀" => polynomialRankOneDeltaStructure σ D
local notation "c₀" => deltaRootRelationFamily (p := p) b
local notation "K₀" => Ideal.span {(p : L₀), MvPolynomial.C (MvPolynomial.C d)}
local notation "Q₀" => L₀ ⧸ K₀
local notation "I₀" => Ideal.span {(p : A), d}
local notation "R₀" => A ⧸ I₀
local notation "q₀" => Ideal.Quotient.mk I₀
local notation "κ₀" => deltaRootSourceQuotientCoefficientMap (σ := σ) (p := p) d
local notation "α₀" => deltaDivisionSourceMap (σ := σ) E₀ (MvPolynomial.C d)
local notation "ψ₀" => RingHom.comp (Ideal.Quotient.mk K₀) α₀
local notation "F₀" => deltaDivisionEvaluationSourceFiniteModuleDiagram E₀ c₀
local notation "Res₀" => DeltaAdjoinDivisionResidue E₀ (MvPolynomial.C d) c₀
local notation "X₀" => DeltaRootSourceIteratedPDCompletion D d b
local notation "MRes" => CategoryTheory.Functor.obj (ModuleCat.restrictScalars κ₀)
  (ModuleCat.of Q₀ Res₀)

local notation "qₙ" =>
  Ideal.Quotient.mk (Ideal.span (Set.insert (p : A) (Set.singleton (d ^ n))))
local notation "rₙ" => prismaticPowerResidueMap (p : A) d n hn
local notation "Z₀" => CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange rₙ)
  (CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange qₙ) X₀)

local notation "Tₙ" => A ⧸ Ideal.span (Set.insert (p : A) (Set.singleton (d ^ n)))
local notation "Kₙ" => prismaticPowerResidueIdeal (p : A) d n
local notation "Sₙ" => Tₙ ⧸ Kₙ
local notation "eₙ" => prismaticPowerResidueQuotientEquiv (p : A) d n hn
local notation "Y₀" => CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange qₙ) X₀
local notation "W₀" => CategoryTheory.Functor.obj
  (boundedAboveDerivedBaseChange (Ideal.Quotient.mk Kₙ)) Y₀
local notation "MCan" => CategoryTheory.Functor.obj
  (ModuleCat.restrictScalars (RingEquiv.toRingHom eₙ)) MRes

/-- G10の標準冪零商による実還元は、商環上の標準raw加群のsingle対象。 -/
def deltaRootSourceCanonicalPowerResidueIso_of_preservesColimit
    (hpA : Function.Injective (fun x : A => (p : A) * x)) (hd : IsSMulRegular A d)
    (hg : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (hpres : ∀ i : ℕ, PreservesColimit F₀
      ((ModuleCat.extendScalars.{u, u, u} ψ₀).leftDerived (i + 1))) :
    letI := (deltaRootSourceQuotientResidueMap D d b).toAlgebra
    letI : Module Q₀ Res₀ := Algebra.toModule
    W₀ ≅ boundedAboveDerivedSingleFunctor.obj MCan := by
  letI := (deltaRootSourceQuotientResidueMap D d b).toAlgebra
  letI : Module Q₀ Res₀ := Algebra.toModule
  exact prismaticPowerResidueCanonicalDerivedIso (p : A) d n hn Y₀ ≪≫
    (boundedAboveDerivedRestrictScalars (eₙ).toRingHom).mapIso
      (deltaRootSourcePowerResidueIso_of_preservesColimit D d b n hn hpA hd hg v hv hpres) ≪≫
    ObjectProperty.isoMk _ ((derivedRestrictScalarsSingleIso (eₙ).toRingHom 0).app MRes)

include hn in
/-- 標準冪零商による実還元の非零次数ホモロジーは零。 -/
theorem deltaRootSourceCanonicalPowerResidue_homology_isZero_of_preservesColimit
    (hpA : Function.Injective (fun x : A => (p : A) * x)) (hd : IsSMulRegular A d)
    (hg : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (hpres : ∀ i : ℕ, PreservesColimit F₀
      ((ModuleCat.extendScalars.{u, u, u} ψ₀).leftDerived (i + 1))) (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat Sₙ) i).obj (W₀).obj) := by
  let := (deltaRootSourceQuotientResidueMap D d b).toAlgebra
  let : Module Q₀ Res₀ := Algebra.toModule
  exact (derivedSingleHomology_isZero MCan i hi).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat Sₙ) i).mapIso
      (DerivedCategory.Minus.ι.mapIso
        (deltaRootSourceCanonicalPowerResidueIso_of_preservesColimit
          D d b n hn hpA hd hg v hv hpres)))

include hn in
/-- 標準冪零商による実還元のH0は、その正確な商環上で忠実平坦。 -/
theorem deltaRootSourceCanonicalPowerResidueH0_faithfullyFlat_of_preservesColimit
    (hpA : Function.Injective (fun x : A => (p : A) * x)) (hd : IsSMulRegular A d)
    (hg : Function.Injective (WittVector.ghostMap : WittVector p L₀ → ℕ → L₀))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (hpres : ∀ i : ℕ, PreservesColimit F₀
      ((ModuleCat.extendScalars.{u, u, u} ψ₀).leftDerived (i + 1))) :
    Module.FaithfullyFlat Sₙ
      ((DerivedCategory.homologyFunctor (ModuleCat Sₙ) 0).obj (W₀).obj) := by
  let M := (DerivedCategory.homologyFunctor (ModuleCat R₀) 0).obj (Z₀).obj
  let eH : (DerivedCategory.homologyFunctor (ModuleCat Sₙ) 0).obj (W₀).obj ≅
      (ModuleCat.restrictScalars (eₙ).toRingHom).obj M :=
    (DerivedCategory.homologyFunctor (ModuleCat Sₙ) 0).mapIso
        (DerivedCategory.Minus.ι.mapIso
          (prismaticPowerResidueCanonicalDerivedIso (p : A) d n hn Y₀)) ≪≫
      (derivedRestrictScalarsHomologyIso (eₙ).toRingHom 0).app (Z₀).obj
  let := (eₙ).toRingHom.toAlgebra
  let : Module Sₙ M := Module.compHom M (eₙ).toRingHom
  let : IsScalarTower Sₙ R₀ M := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let eA : Sₙ ≃ₐ[Sₙ] R₀ :=
    AlgEquiv.ofBijective (Algebra.ofId Sₙ R₀) (eₙ).bijective
  have : Module.FaithfullyFlat Sₙ R₀ :=
    Module.FaithfullyFlat.of_linearEquiv Sₙ Sₙ eA.symm.toLinearEquiv
  have : Module.FaithfullyFlat R₀ M :=
    deltaRootSourcePowerResidueH0_faithfullyFlat_of_preservesColimit
      D d b n hn hpA hd hg v hv hpres
  have : Module.FaithfullyFlat Sₙ M := Module.FaithfullyFlat.trans Sₙ R₀ M
  exact Module.FaithfullyFlat.of_linearEquiv Sₙ M eH.toLinearEquiv

end SerrePositivity.BhattScholze
