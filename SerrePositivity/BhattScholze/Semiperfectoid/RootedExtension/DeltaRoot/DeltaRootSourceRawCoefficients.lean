module

public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.DeltaRoot.DeltaRootSourceRawComparison
public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.DeltaRoot.DeltaRootPrismBaseMap

/-! # raw r/d包の標準A作用と既存prism候補への実導来源射 -/

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
local notation "β" => deltaDivisionSourceEval E r
local notation "Raw" => DeltaAdjoinDivision E (MvPolynomial.C d) r
local notation "j" => deltaAdjoinDivisionMap E (MvPolynomial.C d) r
local notation "C₀" => algebraMap A L

/-- 評価βを経由する制限作用と、raw環の標準A作用の恒等線形同型。 -/
def deltaRootSourceRawCoefficientModuleIso :
    (ModuleCat.restrictScalars C₀).obj (DeltaRootSourceRawModule D d b) ≅
      ModuleCat.of A Raw := by
  let e : (ModuleCat.restrictScalars C₀).obj (DeltaRootSourceRawModule D d b) ≃ₗ[A] Raw :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := by
        intro a x
        rw [RingHom.id_apply, ModuleCat.restrictScalars.smul_def]
        change Raw at x
        change j (β (MvPolynomial.C (MvPolynomial.C a))) * x = a • x
        rw [Algebra.smul_def, deltaDivisionSourceEval_C]
        rfl }
  exact e.toModuleIso

/-- 元のAへの実係数制限後のraw対象を、標準A作用付きraw環の次数零対象へ戻す。 -/
def deltaRootSourceRawCoefficientSingleIso :
    DeltaRootSourceRawCoefficientObject D d b ≅
      boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A Raw) :=
  ObjectProperty.isoMk _
    ((derivedRestrictScalarsSingleIso C₀ 0).app (DeltaRootSourceRawModule D d b) ≪≫
      (DerivedCategory.singleFunctor (ModuleCat A) 0).mapIso
        (deltaRootSourceRawCoefficientModuleIso D d b))

set_option maxHeartbeats 800000 in
-- Keep the original derived tensor and both coefficient restrictions explicit in H0.
/-- 元の実導来源のH0は、標準A作用付きraw r/d環と線形同型。 -/
def deltaRootSourceRawStandardH0Iso :
    (DerivedCategory.homologyFunctor (ModuleCat A) 0).obj
        (DeltaRootSourceCoefficientObject d D b).obj ≅ ModuleCat.of A Raw :=
  deltaRootSourceRawCoefficientH0Iso D d b ≪≫ deltaRootSourceRawCoefficientModuleIso D d b

/-- 既存prism台環候補の標準係数射によるA代数構造。 -/
abbrev deltaRootPrismCoefficientAlgebra :
    letI := deltaRootPrismCommRing D d b
    Algebra A (DeltaRootPrismCarrier D d b) := by
  letI := deltaRootPrismCommRing D d b
  exact (deltaRootPrismCoefficientMap D d b).toAlgebra

/-- 既存raw環射は、元のAの標準係数作用について線形。 -/
def deltaRootSourceRawCandidateLinearMap :
    letI := deltaRootPrismCommRing D d b
    letI := deltaRootPrismCoefficientAlgebra D d b
    letI : Module A (DeltaRootPrismCarrier D d b) := Algebra.toModule
    Raw →ₗ[A] DeltaRootPrismCarrier D d b := by
  letI := deltaRootPrismCommRing D d b
  letI := deltaRootPrismCoefficientAlgebra D d b
  letI : Module A (DeltaRootPrismCarrier D d b) := Algebra.toModule
  exact
    { toFun := deltaRootPrismRawMap D d b
      map_add' := (deltaRootPrismRawMap D d b).map_add
      map_smul' := by
        intro a x
        simp only [RingHom.id_apply, Algebra.smul_def]
        change deltaRootPrismRawMap D d b (algebraMap A Raw a * x) =
          deltaRootPrismCoefficientMap D d b a * deltaRootPrismRawMap D d b x
        rw [map_mul]
        rfl }

/-- 既存候補台環を、標準A係数作用で次数零に置いた実導来対象。 -/
abbrev DeltaRootPrismCoefficientObject : DerivedCategory.Minus (ModuleCat.{u} A) := by
  letI := deltaRootPrismCommRing D d b
  letI := deltaRootPrismCoefficientAlgebra D d b
  letI : Module A (DeltaRootPrismCarrier D d b) := Algebra.toModule
  exact boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A (DeltaRootPrismCarrier D d b))

/-- 元の実二因子導来源から、既存候補の実次数零対象への標準比較射。 -/
def deltaRootSourceCandidateMap :
    DeltaRootSourceCoefficientObject d D b ⟶ DeltaRootPrismCoefficientObject D d b := by
  letI := deltaRootPrismCommRing D d b
  letI := deltaRootPrismCoefficientAlgebra D d b
  letI : Module A (DeltaRootPrismCarrier D d b) := Algebra.toModule
  exact deltaRootSourceRawCoefficientAugmentation D d b ≫
    (deltaRootSourceRawCoefficientSingleIso D d b).hom ≫
    boundedAboveDerivedSingleFunctor.map
      (ModuleCat.ofHom (deltaRootSourceRawCandidateLinearMap D d b))

end SerrePositivity.BhattScholze
