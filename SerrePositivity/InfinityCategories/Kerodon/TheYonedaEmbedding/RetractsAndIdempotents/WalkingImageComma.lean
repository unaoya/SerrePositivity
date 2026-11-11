module

public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.Walking
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingAbsorption
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingImageUniversal

/-!
概要：元の分裂対象から元の冪等包含への comma は、元の冪等添字と同型。
方針：元の射影の逆を、元の唯一の吸収射を付ける関手で構成する。
規約：元の対象・射の等式を証明し、通常圏の同値だけで置き換えない。
使われ方：HTT 4.4.5.11 の元の包含の cofinal 判定。

対応節は Kerodon 8.5（Tag 03Y9）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-- 元の対象に、元の分裂対象からの唯一の吸収射を付ける関手。 -/
def walkingImageCommaSection : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingIdem.{u} ⥤ StructuredArrow _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingImage _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingInclusion where
  obj P := StructuredArrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingAbsorbingHom _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingImage (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingInclusion.obj P))
  map f := StructuredArrow.homMk f (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingAbsorbingHom_comp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingInclusion.map f))
  map_id _ := StructuredArrow.hom_ext _ _ rfl
  map_comp _ _ := StructuredArrow.hom_ext _ _ rfl

/-- 元の comma に元の射影とその逆を適用すると、元の対象を厳密に回収する。 -/
lemma walkingImageCommaSection_obj (c : StructuredArrow _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingImage.{u} _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingInclusion) :
    walkingImageCommaSection.obj c.right = c := by
  refine StructuredArrow.obj_ext (walkingImageCommaSection.obj c.right) c rfl ?_
  simp only [eqToHom_refl]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingHom_from_image c.hom).symm

/-- 元の射影後に元の逆を適用した全関手は、元の恒等関手そのもの。 -/
lemma walkingImageComma_proj_section :
    StructuredArrow.proj _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingImage _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingInclusion ⋙ walkingImageCommaSection.{u} = 𝟭 _ := by
  refine CategoryTheory.Functor.ext walkingImageCommaSection_obj ?_
  intro c d f
  apply StructuredArrow.hom_ext
  simp only [StructuredArrow.comp_right, StructuredArrow.eqToHom_right]
  change f.right = eqToHom rfl ≫ f.right ≫ eqToHom rfl
  simp

/-- 元の分裂対象からの comma と元の冪等添字の、元の射影による圏同型。 -/
def walkingImageCommaIso : Cat.of (StructuredArrow _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingImage.{u} _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingInclusion) ≅
    Cat.of _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingIdem where
  hom := (StructuredArrow.proj _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingImage _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingInclusion).toCatHom
  inv := walkingImageCommaSection.toCatHom
  hom_inv_id := by
    apply Cat.Hom.ext
    exact walkingImageComma_proj_section
  inv_hom_id := by apply Cat.Hom.ext; rfl

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
