module

public import SerrePositivity.AlgebraicGeometry.AffineNilImmersionFrobeniusCoefficients

/-!
概要：nil 閉厚化のアフィン開上の実際の切断写像は普遍同相。
方針：制限の appTop と app U の間の環同型を明示して移す。
規約：appTop と app U を定義的に同一視しない。
使われ方：非空アフィン交叉上での Frobenius 係数の同型（計画 N02）。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
universe u
set_option backward.isDefEq.respectTransparency false

/-- nil 閉厚化のアフィン開上の元の app U は環の普遍同相。 -/
theorem nilImmersion_app_universalHomeomorphism
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f] [Surjective f]
    (U : Y.Opens) (hU : IsAffineOpen U) :
    SerrePositivity.CommutativeAlgebra.IsUniversalHomeomorphism (f.app U).hom := by
  let m := X.presheaf.map (eqToHom (image_morphismRestrict_preimage f U ⊤)).op
  haveI : IsIso m := by dsimp [m]; infer_instance
  have hm : Function.Injective m.hom :=
    ((ConcreteCategory.isIso_iff_bijective m).mp inferInstance).1
  have hc : SerrePositivity.CommutativeAlgebra.IsUniversalHomeomorphism
      (m.hom.comp (f.app (U.ι ''ᵁ ⊤)).hom) := by
    simpa only [morphismRestrict_appTop, CommRingCat.hom_comp] using
      affineNilImmersion_restrict_appTop_universalHomeomorphism f U hU
  have hf := SerrePositivity.CommutativeAlgebra.isUniversalHomeomorphism_tower_bot
    (f.app (U.ι ''ᵁ ⊤)).hom m.hom hc hm
  exact Eq.mp
    (congrArg (fun V : Y.Opens ↦
      SerrePositivity.CommutativeAlgebra.IsUniversalHomeomorphism (f.app V).hom)
      U.ι_image_top) hf

end SerrePositivity.AlgebraicGeometry
