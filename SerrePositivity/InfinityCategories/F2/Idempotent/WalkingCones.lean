module

public import SerrePositivity.InfinityCategories.F2.Idempotent.WalkingAbsorption
public import Mathlib.CategoryTheory.Limits.Cones

/-!
概要：元の冪等添字の包含は、同じ分裂対象を頂点とする元の錐と余錐を持つ。
方針：全ての脚を元の吸収射で指定し、全ての元の射について自然性を証明する。
規約：指定した元の対象では、元の包含と元の射影そのものを回収する。
使われ方：強い coherent 分裂を、同じ全 Idem 図式の錐と余錐へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 元の全冪等図式の包含から、元の分裂対象への元の余錐。 -/
def walkingCocone : Cocone walkingInclusion.{u} where
  pt := walkingImage
  ι :=
    { app P := walkingAbsorbingHom (walkingInclusion.obj P) walkingImage
      naturality _ _ f := by
        change walkingInclusion.map f ≫ walkingAbsorbingHom _ _ = _ ≫ 𝟙 _
        rw [comp_walkingAbsorbingHom, Category.comp_id]
        rfl }

/-- 元の分裂対象から、元の全冪等図式の包含への元の錐。 -/
def walkingCone : Cone walkingInclusion.{u} where
  pt := walkingImage
  π :=
    { app P := walkingAbsorbingHom walkingImage (walkingInclusion.obj P)
      naturality _ _ f := by
        change 𝟙 _ ≫ walkingAbsorbingHom _ _ = walkingAbsorbingHom _ _ ≫ walkingInclusion.map f
        rw [Category.id_comp, walkingAbsorbingHom_comp] }

/-- 元の余錐の指定した対象での脚は、元の射影そのもの。 -/
lemma walkingCocone_leg : walkingCocone.{u}.ι.app walkingObject = walkingRetraction := rfl

/-- 元の錐の指定した対象での脚は、元の包含そのもの。 -/
lemma walkingCone_leg : walkingCone.{u}.π.app walkingObject = walkingSection := rfl

/-- 元の錐の脚と元の余錐の脚の合成は、元の分裂対象の恒等。 -/
lemma walkingCone_cocone :
    walkingCone.{u}.π.app walkingObject ≫ walkingCocone.ι.app walkingObject = 𝟙 walkingImage :=
  walkingSection_retraction

/-- 逆順の合成は、元の指定した非恒等冪等射の包含像。 -/
lemma walkingCocone_cone :
    walkingCocone.{u}.ι.app walkingObject ≫ walkingCone.π.app walkingObject =
      walkingInclusion.map walkingIdempotent := walkingRetraction_section

end SerrePositivity.InfinityCategories.F2.Idempotent
