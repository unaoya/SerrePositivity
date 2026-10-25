module

public import SerrePositivity.BhattScholze.Prism.PerfectDeltaFrobeniusModels
public import SerrePositivity.HomologicalAlgebra.BaseChangeEquivalence

/-! # 実Frobenius係数制限とprism係数商の導来可換図式 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (D : DeltaStructure p A) (hD : D.IsPerfect) (d : A) (n : ℕ)
local notation "e" => RingEquiv.ofBijective (D.frobeniusLift ^ n) (hD.iterate n)
local notation "κ" => perfectDeltaFrobeniusPrismaticResidueEquiv D hD d n
local notation "I₀" => Ideal.span {(p : A), d}
local notation "Jₙ" => Ideal.span {(p : A), (D.frobeniusLift ^ n) d}
local notation "q₀" => Ideal.Quotient.mk I₀
local notation "qₙ" => Ideal.Quotient.mk Jₙ

/-- 逆Frobeniusと実標準商射の係数図式。 -/
theorem perfectDeltaFrobeniusQuotient_inverse_square :
    (q₀).comp (e).symm.toRingHom = (κ).symm.toRingHom.comp qₙ := by
  apply RingHom.ext
  intro x
  rfl

/-- 実φⁿ制限後の標準係数拡大と、移動した商への拡大後の正確な係数制限の比較。 -/
def perfectDeltaFrobeniusQuotientScalarIso :
    ModuleCat.restrictScalars (e).toRingHom ⋙ ModuleCat.extendScalars q₀ ≅
      ModuleCat.extendScalars qₙ ⋙ ModuleCat.restrictScalars (κ).toRingHom :=
  Functor.isoWhiskerRight (restrictScalarsIsoExtendInverse e) (ModuleCat.extendScalars q₀) ≪≫
    (ModuleCat.extendScalarsComp (e).symm.toRingHom q₀).symm ≪≫
    eqToIso (congrArg ModuleCat.extendScalars
      (perfectDeltaFrobeniusQuotient_inverse_square D hD d n)) ≪≫
    ModuleCat.extendScalarsComp qₙ (κ).symm.toRingHom ≪≫
    Functor.isoWhiskerLeft (ModuleCat.extendScalars qₙ) (restrictScalarsIsoExtendInverse κ).symm

/-- 同じ通常関手squareを、実際の射影複体の各項へ適用する。 -/
def perfectDeltaFrobeniusQuotientCochainIso (K : CochainComplex (ModuleCat.{u} A) ℤ) :
    baseChange q₀
      (((ModuleCat.restrictScalars (e).toRingHom).mapHomologicalComplex (.up ℤ)).obj K) ≅
        ((ModuleCat.restrictScalars (κ).toRingHom).mapHomologicalComplex (.up ℤ)).obj
          (baseChange qₙ K) :=
  (Functor.mapHomologicalComplexCompIso
    (perfectDeltaFrobeniusQuotientScalarIso D hD d n) (.up ℤ)).app K

/-- 指定した同じ実射影モデル上で、Frobeniusねじれ源の実係数商還元を計算する。 -/
def perfectDeltaFrobeniusQuotientDerivedIso
    (X : DerivedCategory.Minus (ModuleCat.{u} A)) (P : BoundedAboveDerivedModel X.obj) :
    (boundedAboveDerivedBaseChange q₀).obj
      ((boundedAboveDerivedRestrictScalars (e).toRingHom).obj X) ≅
        (boundedAboveDerivedRestrictScalars (κ).toRingHom).obj
          ((boundedAboveDerivedBaseChange qₙ).obj X) :=
  ObjectProperty.isoMk _
    (perfectDeltaFrobeniusRestrictQuotientModelIso D hD n I₀ X P ≪≫
      DerivedCategory.Q.mapIso (perfectDeltaFrobeniusQuotientCochainIso D hD d n P.complex) ≪≫
        ((derivedRestrictScalarsFactors (κ).toRingHom).app
          (baseChange qₙ P.complex)).symm ≪≫
        (derivedRestrictScalars (κ).toRingHom).mapIso
          (boundedAboveDerivedBaseChangeModelIso qₙ X P).symm)

end SerrePositivity.BhattScholze
