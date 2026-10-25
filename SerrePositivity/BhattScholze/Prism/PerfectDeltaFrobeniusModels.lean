module

public import SerrePositivity.BhattScholze.Prism.PerfectDeltaPrismaticResidue
public import SerrePositivity.HomologicalAlgebra.BoundedAboveDerivedBaseChange
public import SerrePositivity.HomologicalAlgebra.DerivedRestriction
public import Mathlib.CategoryTheory.Preadditive.Projective.Preserves

/-! # 実Frobenius係数制限による射影モデルの移送 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (D : DeltaStructure p A) (hD : D.IsPerfect) (n : ℕ)
local notation "e" => RingEquiv.ofBijective (D.frobeniusLift ^ n) (hD.iterate n)
local notation "F" => ModuleCat.restrictScalars (RingEquiv.toRingHom e)

/-- 実φⁿの係数制限は、環同値による圏同値として射影加群を保つ。 -/
theorem perfectDeltaFrobeniusRestrict_projective (M : ModuleCat.{u} A) [Projective M] :
    Projective ((F).obj M) := by
  let : (F).IsEquivalence := ModuleCat.restrictScalars_isEquivalence_of_ringEquiv e
  exact (F).projective_obj_of_projective inferInstance

/-- 指定した実射影モデルを、実φⁿ係数制限対象の射影モデルへ移す。 -/
def perfectDeltaFrobeniusRestrictModel
    (X : DerivedCategory.Minus (ModuleCat.{u} A)) (P : BoundedAboveDerivedModel X.obj) :
    BoundedAboveDerivedModel
      (((boundedAboveDerivedRestrictScalars (e).toRingHom).obj X).obj) where
  complex := ((F).mapHomologicalComplex (.up ℤ)).obj P.complex
  bound := P.bound
  bounded := inferInstance
  projective i := perfectDeltaFrobeniusRestrict_projective D hD n (P.complex.X i)
  iso := (boundedAboveDerivedRestrictScalarsModelIso (e).toRingHom X P).symm

/-- 元の係数イデアルによる実還元は、移した同じ射影モデルで計算できる。 -/
def perfectDeltaFrobeniusRestrictQuotientModelIso (I : Ideal A)
    (X : DerivedCategory.Minus (ModuleCat.{u} A)) (P : BoundedAboveDerivedModel X.obj) :
    ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk I)).obj
      ((boundedAboveDerivedRestrictScalars (e).toRingHom).obj X)).obj ≅
        DerivedCategory.Q.obj (baseChange (Ideal.Quotient.mk I)
          (((F).mapHomologicalComplex (.up ℤ)).obj P.complex)) :=
  boundedAboveDerivedBaseChangeModelIso (Ideal.Quotient.mk I) _
    (perfectDeltaFrobeniusRestrictModel D hD n X P)

end SerrePositivity.BhattScholze
