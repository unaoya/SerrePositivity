module

public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.Walking
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingAbsorption
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingImageUniversal

/-!
概要：元の冪等包含から元の分裂対象への comma は、元の冪等添字と同型。
方針：元の射影の逆を、元の唯一の吸収射を付ける関手で構成する。
規約：元の対象・射の等式を証明し、通常圏の同値だけで置き換えない。
使われ方：HTT 4.4.5.13 の元の包含の cofinal 判定。

対応節は Kerodon 8.5（Tag 03Y9）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-- 元の対象に、元の分裂対象への唯一の吸収射を付ける関手。 -/
def walkingImageLeftCommaSection :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingIdem.{u} ⥤ CostructuredArrow _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingInclusion _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingImage where
  obj P := CostructuredArrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingAbsorbingHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingInclusion.obj P) _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingImage)
  map f := CostructuredArrow.homMk f (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.comp_walkingAbsorbingHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingInclusion.map f))
  map_id _ := CostructuredArrow.hom_ext _ _ rfl
  map_comp _ _ := CostructuredArrow.hom_ext _ _ rfl

/-- 元の comma に元の射影とその逆を適用すると、元の対象を厳密に回収する。 -/
lemma walkingImageLeftCommaSection_obj (c : CostructuredArrow _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingInclusion _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingImage.{u}) :
    walkingImageLeftCommaSection.obj c.left = c := by
  refine CostructuredArrow.obj_ext (walkingImageLeftCommaSection.obj c.left) c rfl ?_
  have h := congrArg (fun f ↦ f ≫ c.hom) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingInclusion.map_id c.left)
  exact h.trans ((Category.id_comp _).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingHom_to_image c.hom))

/-- 元の射影後に元の逆を適用した全関手は、元の恒等関手そのもの。 -/
lemma walkingImageLeftComma_proj_section :
    CostructuredArrow.proj _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingInclusion _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingImage ⋙
      walkingImageLeftCommaSection.{u} = 𝟭 _ := by
  refine CategoryTheory.Functor.ext walkingImageLeftCommaSection_obj ?_
  intro c d f
  apply CostructuredArrow.hom_ext
  simp only [CostructuredArrow.comp_left, CostructuredArrow.eqToHom_left]
  change f.left = eqToHom rfl ≫ f.left ≫ eqToHom rfl
  simp

/-- 元の分裂対象への comma と元の冪等添字の、元の射影による圏同型。 -/
def walkingImageLeftCommaIso : Cat.of (CostructuredArrow _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingInclusion _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingImage.{u}) ≅
    Cat.of _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingIdem where
  hom := (CostructuredArrow.proj _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingInclusion _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingImage).toCatHom
  inv := walkingImageLeftCommaSection.toCatHom
  hom_inv_id := by
    apply Cat.Hom.ext
    exact walkingImageLeftComma_proj_section
  inv_hom_id := by apply Cat.Hom.ext; rfl

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
