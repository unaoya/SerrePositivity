module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WeakMono

/-!
概要：Ret の商模型と、元の強い分裂二単体の像である Ret 部分複体を厳密に同定する。
方針：元の比較の単射性と、元の二単体からの全射性を用いる。
規約：同型の後の包含は元の標準比較そのもの。別の Ret の像に置き換えない。
使われ方：HTT 4.4.5.6 の部分複体の濾過と、弱い retract 図式の延長。

対応節は Kerodon 8.5（Tag 03Y9）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-- 元の強い分裂二単体の像としての Ret 部分複体。 -/
def weakRetractionImage : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.SplitShape.{u}.Subcomplex :=
  Subcomplex.range _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingRetractionTriangle

/-- 元の商からの標準比較の像は、元の分裂二単体の同じ像。 -/
lemma weakComparison_range : Subcomplex.range _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.weakComparison.{u} = weakRetractionImage := by
  have h := congrArg Subcomplex.range _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.weakComparison_triangle.{u}
  rw [Subcomplex.range_comp, Subcomplex.range_eq_top, Subcomplex.image_top] at h
  exact h

/-- 元の Ret の商と元の分裂二単体の像の、元の標準比較から得た同型。 -/
def weakShapeImageIso : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WeakShape.{u} ≅ (weakRetractionImage : SSet.{u}) :=
  asIso (Subcomplex.toRange _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.weakComparison) ≪≫ Subcomplex.eqToIso weakComparison_range

/-- 同型の後の元の包含は、同じ元の標準比較そのもの。 -/
lemma weakShapeImageIso_ι :
    weakShapeImageIso.{u}.hom ≫ weakRetractionImage.ι = _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.weakComparison := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro a
  rfl

/-- 元の二単体を同型へ送ると、元の同じ分裂二単体を元の像へ制限した射となる。 -/
lemma weakTriangle_imageIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.weakTriangle ≫ weakShapeImageIso.{u}.hom ≫ weakRetractionImage.ι =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.walkingRetractionTriangle := by
  rw [weakShapeImageIso_ι, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.weakComparison_triangle]

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
