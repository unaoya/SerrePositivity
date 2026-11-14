module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.RetractionStageColimit
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.RetractionStagePushout
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：元の弱い retract の商から元の強い分裂添字への標準比較は inner anodyne。
方針：元の各段階の pushout による包含を、元の全被覆余錐で無限合成する。
規約：第一段階の像との同型後の包含は、元の標準比較そのもの。
使われ方：任意の quasicategory 内で、元の弱い retract 図式を強い分裂へ延長する。

対応節は Kerodon 8.5（Tag 03Y9）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-- 元の第一段階の包含は、元の各段階包含の可算無限合成。 -/
def retractionStageOne_transfiniteComposition :
    innerAnodyneExtensions.TransfiniteCompositionOfShape ℕ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.retractionStage.{u} 1).ι where
  F := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.retractionStageFunctor
  isoBot := Iso.refl _
  incl := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.retractionStageCocone.ι
  isColimit := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.retractionStageCocone_isColimit
  fac := Category.id_comp _
  map_mem m _hm := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.retractionStageMap_innerAnodyne (m + 1) (by omega)

/-- 元の第一段階の包含そのものは inner anodyne。 -/
lemma retractionStageOne_innerAnodyne : innerAnodyneExtensions (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.retractionStage.{u} 1).ι :=
  MorphismProperty.transfiniteCompositionsOfShape_le innerAnodyneExtensions ℕ _
    ⟨retractionStageOne_transfiniteComposition⟩

/-- 元の弱い retract の商から元の強い分裂添字への同じ標準比較は inner anodyne。 -/
@[kerodon 03Z6]
lemma weakComparison_innerAnodyne : innerAnodyneExtensions _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.weakComparison.{u} := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.weakShapeStageOneIso_ι]
  exact innerAnodyneExtensions.comp_mem _ _
    (innerAnodyneExtensions.of_isIso _) retractionStageOne_innerAnodyne

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "4.4.5.6"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.weakComparison_innerAnodyne
