module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.AlternatingRestriction

/-!
概要：元の交互列の全単体の像から、Ret を始段階とする元の部分複体の増大列を構成する。
方針：元の前半制限の厳密な一致から、元の像の包含と全セルの可換性を回収する。
規約：濾過の全被覆性と各段階の pushout は後続で証明する。
使われ方：HTT 4.4.5.6 の元の Ret 濾過。

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

/-- 元の長さ 2m の交互列の全単体の像としての第 m 段階。 -/
def retractionStage (m : ℕ) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.SplitShape.{u}.Subcomplex := Subcomplex.range (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingCell m)

/-- 元の段階は元の部分複体として増大する。 -/
lemma retractionStage_mono : Monotone retractionStage.{u} := by
  intro m M h
  have hh : Subcomplex.range
      (SSet.stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingPrefix (Nat.mul_le_mul_left 2 h)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingCell M) ≤
        Subcomplex.range (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingCell M) := by
    rw [Subcomplex.range_comp]
    exact Subcomplex.image_le_range _ _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingCell_prefix h] at hh
  exact hh

/-- 元の第一段階は、元の分裂三角形の像である同じ Ret 部分複体。 -/
lemma retractionStage_one : retractionStage.{u} 1 = _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.weakRetractionImage := by
  rw [retractionStage, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingCell_one]
  rfl

/-- 元の Ret の商と、元の第一段階との厳密な同型。 -/
def weakShapeStageOneIso : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WeakShape.{u} ≅ (retractionStage 1 : SSet.{u}) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.weakShapeImageIso ≪≫ Subcomplex.eqToIso retractionStage_one.symm

/-- 元の第一段階への同型の後の包含は、元の同じ標準比較。 -/
lemma weakShapeStageOneIso_ι :
    weakShapeStageOneIso.{u}.hom ≫ (retractionStage 1).ι = _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.weakComparison := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro a
  rfl

/-- 元の増大列の、元の部分複体の包含による構造射。 -/
def retractionStageMap {m M : ℕ} (h : m ≤ M) :
    (retractionStage.{u} m : SSet.{u}) ⟶ retractionStage M :=
  Subcomplex.homOfLE (retractionStage_mono h)

/-- 元の増大列の構造射は、元の同じ周囲の分裂添字への包含と厳密に可換。 -/
lemma retractionStageMap_ι {m M : ℕ} (h : m ≤ M) :
    retractionStageMap.{u} h ≫ (retractionStage M).ι = (retractionStage m).ι := rfl

/-- 元の交互列の全セルを、元の像の段階へ制限する。 -/
def retractionStageCell (m : ℕ) : (Δ[2 * m] : SSet.{u}) ⟶ retractionStage m :=
  Subcomplex.toRange (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingCell m)

/-- 元の段階に制限した全セルは、元の包含後に同じ交互列の全セルを回収する。 -/
lemma retractionStageCell_ι (m : ℕ) :
    retractionStageCell.{u} m ≫ (retractionStage m).ι = _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingCell m := rfl

/-- 元の全セルの前半制限と元の増大列の構造射は、元の同じ全単体で可換。 -/
lemma retractionStageCell_prefix {m M : ℕ} (h : m ≤ M) :
    SSet.stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingPrefix (Nat.mul_le_mul_left 2 h)) ≫ retractionStageCell.{u} M =
      retractionStageCell m ≫ retractionStageMap h := by
  apply (cancel_mono (retractionStage M).ι).mp
  rw [Category.assoc, retractionStageCell_ι, Category.assoc, retractionStageMap_ι,
    retractionStageCell_ι, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingCell_prefix h]

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
