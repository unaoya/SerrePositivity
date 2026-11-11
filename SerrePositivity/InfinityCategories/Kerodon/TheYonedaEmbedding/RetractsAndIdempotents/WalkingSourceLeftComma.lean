module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.Walking

/-!
概要：元の冪等包含から元の非分裂対象への comma は、指定した終対象を持つ。
方針：元の恒等射を対象に選び、元の Karoubi の射の値をそのまま取り出す。
規約：元の comma の射と全可換条件を保持する。
使われ方：HTT 4.4.5.13 の非分裂対象での cofinal 判定。

対応節は Kerodon 8.5（Tag 03Y9）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-- 元の非分裂対象への comma の、元の恒等射による対象。 -/
def walkingSourceLeftCommaPoint : CostructuredArrow _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingInclusion _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingSource.{u} :=
  CostructuredArrow.mk (𝟙 _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingSource)

/-- 元の任意の comma 対象から、元の恒等射の comma 対象への指定射。 -/
def walkingSourceLeftCommaArrow (c : CostructuredArrow _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingInclusion _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingSource.{u}) :
    c ⟶ walkingSourceLeftCommaPoint :=
  CostructuredArrow.homMk c.hom.f (by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingInclusion.map c.hom.f ≫ 𝟙 _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingSource = c.hom
    exact (Category.comp_id _).trans (CategoryTheory.Idempotents.Karoubi.Hom.ext rfl))

/-- 元の非分裂対象への comma の指定した恒等射は終対象。 -/
def walkingSourceLeftComma_isTerminal : IsTerminal walkingSourceLeftCommaPoint.{u} := by
  refine IsTerminal.ofUniqueHom walkingSourceLeftCommaArrow ?_
  intro c f
  apply CostructuredArrow.hom_ext
  have h := CostructuredArrow.w f
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingInclusion.map f.left ≫ 𝟙 _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingSource = c.hom at h
  have he := (Category.comp_id (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingInclusion.map f.left)).symm.trans h
  exact congrArg CategoryTheory.Idempotents.Karoubi.Hom.f he

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
