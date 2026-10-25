module

public import SerrePositivity.BhattScholze.Prism.PrismaticPowerResidueDerived
public import SerrePositivity.HomologicalAlgebra.BaseChangeEquivalence
public import SerrePositivity.HomologicalAlgebra.DerivedRestriction

/-! # G10の標準冪零商射に沿う実還元との比較 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard
variable {A : Type u} [CommRing A] (a d : A) (n : ℕ) (hn : 0 < n)
local notation "Tₙ" => A ⧸ Ideal.span (Set.insert a (Set.singleton (d ^ n)))
local notation "Kₙ" => prismaticPowerResidueIdeal a d n
local notation "qₖ" => Ideal.Quotient.mk Kₙ
local notation "rₙ" => prismaticPowerResidueMap a d n hn
local notation "eₙ" => prismaticPowerResidueQuotientEquiv a d n hn

/-- 冪零商の逆同型は標準剰余射を標準商射へ戻す。 -/
theorem prismaticPowerResidueQuotientEquiv_symm_comp :
    (eₙ).symm.toRingHom.comp rₙ = qₖ := by
  apply RingHom.ext
  intro x
  apply (eₙ).injective
  change (eₙ) ((eₙ).symm ((rₙ) x)) = (eₙ) ((qₖ) x)
  rw [RingEquiv.apply_symm_apply]
  exact (RingHom.congr_fun (prismaticPowerResidueQuotientEquiv_comp_mk a d n hn) x).symm

/-- 標準冪零商への係数拡大は、既存剰余射と商同型による係数制限で計算できる。 -/
def prismaticPowerResidueCanonicalScalarIso :
    ModuleCat.extendScalars qₖ ≅
      ModuleCat.extendScalars rₙ ⋙ ModuleCat.restrictScalars (eₙ).toRingHom :=
  eqToIso (congrArg ModuleCat.extendScalars
      (prismaticPowerResidueQuotientEquiv_symm_comp a d n hn).symm) ≪≫
    ModuleCat.extendScalarsComp rₙ (eₙ).symm.toRingHom ≪≫
      Functor.isoWhiskerLeft (ModuleCat.extendScalars rₙ)
        (restrictScalarsIsoExtendInverse eₙ).symm

/-- 同じ係数比較は複体上でも自然に成立する。 -/
def prismaticPowerResidueCanonicalCochainIso :
    (ModuleCat.extendScalars qₖ).mapHomologicalComplex (.up ℤ) ≅
      (ModuleCat.extendScalars rₙ).mapHomologicalComplex (.up ℤ) ⋙
        (ModuleCat.restrictScalars (eₙ).toRingHom).mapHomologicalComplex (.up ℤ) :=
  (Functor.mapHomologicalComplexCompIso
    (prismaticPowerResidueCanonicalScalarIso a d n hn).symm (.up ℤ)).symm

/-- G10の実標準商還元を、既証の実剰余還元の商同型による係数制限へ比較する。 -/
def prismaticPowerResidueCanonicalDerivedIso
    (X : DerivedCategory.Minus (ModuleCat.{u} Tₙ)) :
    (boundedAboveDerivedBaseChange qₖ).obj X ≅
      (boundedAboveDerivedRestrictScalars (eₙ).toRingHom).obj
        ((boundedAboveDerivedBaseChange rₙ).obj X) :=
  ObjectProperty.isoMk _
    (DerivedCategory.Q.mapIso ((prismaticPowerResidueCanonicalCochainIso a d n hn).app
        (boundedAboveDerivedChosenModel X).complex) ≪≫
      ((derivedRestrictScalarsFactors (eₙ).toRingHom).app
        (baseChange rₙ (boundedAboveDerivedChosenModel X).complex)).symm ≪≫
      (derivedRestrictScalars (eₙ).toRingHom).mapIso
        (boundedAboveDerivedBaseChangeModelIso rₙ X (boundedAboveDerivedChosenModel X)).symm)

end SerrePositivity.BhattScholze
