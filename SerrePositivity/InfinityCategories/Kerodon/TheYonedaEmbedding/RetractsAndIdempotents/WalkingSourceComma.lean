module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.Walking

/-!
概要：元の非分裂対象から元の冪等包含への comma は、指定した始対象を持つ。
方針：元の恒等射を対象に選び、元の Karoubi の射の値をそのまま取り出す。
規約：元の comma の射と全可換条件を保持する。
使われ方：HTT 4.4.5.11 の非分裂対象での cofinal 判定。

対応節は Kerodon 8.5（Tag 03Y9）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-- 元の非分裂対象からの comma の、元の恒等射による対象。 -/
def walkingSourceCommaPoint : StructuredArrow _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingSource.{u} _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingInclusion :=
  StructuredArrow.mk (𝟙 _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingSource)

/-- 元の恒等射の comma 対象から、元の任意の comma 対象への指定射。 -/
def walkingSourceCommaArrow (c : StructuredArrow _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingSource.{u} _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingInclusion) :
    walkingSourceCommaPoint ⟶ c :=
  StructuredArrow.homMk c.hom.f (by
    change 𝟙 _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingSource ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingInclusion.map c.hom.f = c.hom
    rw [Category.id_comp]
    exact CategoryTheory.Idempotents.Karoubi.Hom.ext rfl)

/-- 元の非分裂対象からの comma の指定した恒等射は始対象。 -/
def walkingSourceComma_isInitial : IsInitial walkingSourceCommaPoint.{u} := by
  refine IsInitial.ofUniqueHom walkingSourceCommaArrow ?_
  intro c f
  apply StructuredArrow.hom_ext
  have h := StructuredArrow.w f
  change 𝟙 _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingSource ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingInclusion.map f.right = c.hom at h
  rw [Category.id_comp] at h
  exact congrArg CategoryTheory.Idempotents.Karoubi.Hom.f h

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
