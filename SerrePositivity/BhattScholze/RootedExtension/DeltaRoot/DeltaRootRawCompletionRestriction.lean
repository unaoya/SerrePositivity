module

public import SerrePositivity.BhattScholze.RootedExtension.DeltaRoot.DeltaRootSourceCompletionH0
public import SerrePositivity.BhattScholze.RootedExtension.DeltaRoot.DeltaRootSourceRawCoefficients
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.RestrictionCompletion
public import SerrePositivity.HomologicalAlgebra.AlgebraRestrictionSingle

/-! # raw根環自身の実逐次完備化と元のA上の実対象の比較 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (b : σ → A)
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => deltaRootRelationFamily (p := p) b
local notation "Raw" => DeltaAdjoinDivision E (MvPolynomial.C d) r
local notation "c" => algebraMap A Raw
local notation "M" => CategoryTheory.Functor.obj
  (DerivedCategory.singleFunctor (ModuleCat Raw) 0) (ModuleCat.of Raw Raw)
local notation "Cp" => derivedComplexCompletionFunctor A (p : A)
local notation "Cd" => derivedComplexCompletionFunctor A d
local notation "Bp" => derivedComplexCompletionFunctor Raw (c (p : A))
local notation "Bd" => derivedComplexCompletionFunctor Raw (c d)
local notation "Res" => derivedRestrictScalars c

/-- 元のraw係数対象は、raw環自身のsingleを実係数射で制限した対象。 -/
def deltaRootRawCoefficientRestrictionIso :
    (DeltaRootSourceRawCoefficientObject D d b).obj ≅ (Res).obj M :=
  DerivedCategory.Minus.ι.mapIso (deltaRootSourceRawCoefficientSingleIso D d b) ≪≫
    (algebraRestrictionSingleIso A Raw).symm

/-- raw環自身の二つの主元についての実逐次完備化。 -/
abbrev DeltaRootRawInternalIteratedCompletion := (Bd).obj ((Bp).obj M)

/-- 二度のG8を同じ係数射に適用した、元のraw実逐次対象との同型。 -/
def deltaRootRawIteratedRestrictionIso :
    (DeltaRootSourceRawIteratedCompletion D d b).obj ≅
      (Res).obj (DeltaRootRawInternalIteratedCompletion D d b) :=
  (Cd).mapIso ((Cp).mapIso (deltaRootRawCoefficientRestrictionIso D d b)) ≪≫
    (Cd).mapIso ((derivedCompletionRestrictionIso c (p : A)).app M) ≪≫
    (derivedCompletionRestrictionIso c d).app ((Bp).obj M)

/-- 係数比較は両方の元の主元完備化単位を保つ。 -/
theorem deltaRootRawIteratedRestrictionIso_unit :
    ((derivedComplexCompletionUnit A (p : A)).app
        (DeltaRootSourceRawCoefficientObject D d b).obj ≫
      (derivedComplexCompletionUnit A d).app
        ((Cp).obj (DeltaRootSourceRawCoefficientObject D d b).obj)) ≫
      (deltaRootRawIteratedRestrictionIso D d b).hom =
    (deltaRootRawCoefficientRestrictionIso D d b).hom ≫
      (Res).map ((derivedComplexCompletionUnit Raw (c (p : A))).app M ≫
        (derivedComplexCompletionUnit Raw (c d)).app ((Bp).obj M)) := by
  let e := deltaRootRawCoefficientRestrictionIso D d b
  let eP := (Cp).mapIso e ≪≫ (derivedCompletionRestrictionIso c (p : A)).app M
  have hp : (derivedComplexCompletionUnit A (p : A)).app
      (DeltaRootSourceRawCoefficientObject D d b).obj ≫ eP.hom =
      e.hom ≫ (Res).map ((derivedComplexCompletionUnit Raw (c (p : A))).app M) := by
    have hn := (derivedComplexCompletionUnit A (p : A)).naturality e.hom
    simp only [Functor.id_map] at hn
    dsimp only [eP, Iso.trans_hom, Functor.mapIso_hom]
    rw [← Category.assoc, ← hn, Category.assoc]
    erw [derivedCompletionRestrictionIso_unit]
  have hd := (derivedComplexCompletionUnit A d).naturality eP.hom
  simp only [Functor.id_map] at hd
  have he : (deltaRootRawIteratedRestrictionIso D d b).hom =
      (Cd).map eP.hom ≫ (derivedCompletionRestrictionIso c d).hom.app ((Bp).obj M) := by
    simp only [deltaRootRawIteratedRestrictionIso, eP, e, Iso.trans_hom,
      Functor.mapIso_hom, Functor.map_comp, Category.assoc]
    rfl
  rw [he]
  simp only [Category.assoc]
  rw [← Category.assoc ((derivedComplexCompletionUnit A d).app _) ((Cd).map eP.hom),
    ← hd]
  simp only [Category.assoc]
  erw [derivedCompletionRestrictionIso_unit]
  rw [← Category.assoc, hp, Category.assoc, ← Functor.map_comp]

/-- raw環上の同じ実逐次完備化のH0へ、元のA作用を保って比較する。 -/
def deltaRootRawIteratedRestrictionH0Iso :
    (DerivedCategory.homologyFunctor (ModuleCat A) 0).obj
        (DeltaRootSourceRawIteratedCompletion D d b).obj ≅
      (ModuleCat.restrictScalars c).obj
        ((DerivedCategory.homologyFunctor (ModuleCat Raw) 0).obj
          (DeltaRootRawInternalIteratedCompletion D d b)) :=
  (DerivedCategory.homologyFunctor (ModuleCat A) 0).mapIso
    (deltaRootRawIteratedRestrictionIso D d b) ≪≫
      (derivedRestrictScalarsHomologyIso c 0).app _

/-- 元の実根添加源のH0をraw環上の実逐次完備化のH0と同定する。 -/
def deltaRootSourceInternalRawH0Iso :
    (DerivedCategory.homologyFunctor (ModuleCat A) 0).obj
        (DeltaRootSourceIteratedPDCompletion D d b).obj ≅
      (ModuleCat.restrictScalars c).obj
        ((DerivedCategory.homologyFunctor (ModuleCat Raw) 0).obj
          (DeltaRootRawInternalIteratedCompletion D d b)) :=
  deltaRootSourceRawIteratedH0Iso D d b ≪≫ deltaRootRawIteratedRestrictionH0Iso D d b

end SerrePositivity.BhattScholze
