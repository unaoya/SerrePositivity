module

public import SerrePositivity.AlgebraicGeometry.FilteredPushoutRingModel
public import SerrePositivity.AlgebraicGeometry.AffineVCoverBaseChange
public import Mathlib.RingTheory.RingHom.FiniteType
public import Mathlib.RingTheory.RingHomProperties

/-!
概要：係数段の pushout の第一挿入に、固定した射の被覆性と有限型性を移す。
方針：実際の pushout 正方形に、v 判定と有限型性の底変換安定性を適用する。
規約：係数射に忠実平坦性を要求しない。
使われ方：B03・B04 の有限型被覆模型を動かした全ての後段の性質。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory Limits
universe u
variable {J : Type u} [SmallCategory J] [IsFiltered J]
  {A B : CommRingCat.{u}} (F : J ⥤ CommRingCat.{u})
  (α : (Functor.const J).obj A ⟶ F) (f : A ⟶ B)

/-- 固定した射が affine v 被覆なら、全ての係数段の第一挿入も affine v 被覆。 -/
theorem filteredPushoutRingInl_vCover (hf : IsAffineVCover f.hom) (j : J) :
    IsAffineVCover ((filteredPushoutRingInl F α f).app j).hom :=
  IsAffineVCover.baseChange (α.app j).hom (pushout.inr (α.app j) f).hom
    (pushout.inl (α.app j) f).hom (IsPushout.of_hasPushout (α.app j) f).flip hf

/-- 固定した射が有限型なら、全ての係数段の第一挿入も有限型。 -/
theorem filteredPushoutRingInl_finiteType (hf : f.hom.FiniteType) (j : J) :
    ((filteredPushoutRingInl F α f).app j).hom.FiniteType := by
  letI : (RingHom.toMorphismProperty RingHom.FiniteType).IsStableUnderCobaseChange :=
    RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.mpr
      RingHom.finiteType_isStableUnderBaseChange
  exact MorphismProperty.of_isPushout (P := RingHom.toMorphismProperty RingHom.FiniteType)
    (IsPushout.of_hasPushout (α.app j) f) hf

end SerrePositivity.AlgebraicGeometry
