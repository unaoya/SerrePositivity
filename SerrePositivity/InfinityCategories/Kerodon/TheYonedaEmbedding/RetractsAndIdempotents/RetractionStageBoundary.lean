module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.OddDeletion
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.AlternatingCellBoundary

/-!
概要：元の交互セルの境界全体を、元の Ret の前段階へ制限する。
方針：奇数頂点を一つ避ける各面の元の短い交互列への因子化を合併する。
規約：元の包含と全セルを持つ可換な正方形を構成し、pushout 性は後で証明する。
使われ方：HTT 4.4.5.6 の元の段階の貼付けの前半。

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

/-- 元の奇数頂点を避ける面の全交互セルの像は、元の前段階に入る。 -/
lemma alternatingCell_oddFace_image_le {m : ℕ} (j : Fin (2 * m + 3)) (hj : j.val % 2 = 1) :
    (stdSimplex.face {j}ᶜ).image (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingCell.{u} (m + 1)) ≤ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.retractionStage m := by
  rw [← stdSimplex.range_δ, ← Subcomplex.range_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingCell_oddFace j hj,
    Subcomplex.range_comp]
  exact Subcomplex.image_le_range _ _

/-- 元の境界の全単体の像は、元の Ret の前段階に入る。 -/
lemma alternatingCellBoundary_image_le (m : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingCellBoundary.{u} (m + 1)).image (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingCell (m + 1)) ≤
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.retractionStage m := by
  apply (Subcomplex.image_le_iff _ _ _).mpr
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingCellBoundary, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.missingFaceComplex]
  apply iSup_le
  intro j
  apply iSup_le
  intro hj
  exact (Subcomplex.image_le_iff _ _ _).mp
    (alternatingCell_oddFace_image_le j (Finset.mem_filter.mp hj).2)


/-- 元の交互セルの前段階の逆像は、元の境界全体を含む。 -/
lemma alternatingCellBoundary_le_preimage (m : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingCellBoundary.{u} (m + 1) ≤
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.retractionStage m).preimage (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingCell (m + 1)) :=
  (Subcomplex.image_le_iff _ _ _).mp (alternatingCellBoundary_image_le m)

/-- 元の境界の全交互セルを、元の前段階へ制限する実際の写像。 -/
def alternatingCellBoundaryLift (m : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingCellBoundary.{u} (m + 1) : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.retractionStage m :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.retractionStage m).lift
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingCellBoundary (m + 1)).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingCell (m + 1)) (by
      rw [← Subcomplex.image_eq_range]
      exact alternatingCellBoundary_image_le m)

/-- 元の境界から前段階への制限は、元の包含後に同じ全セルの制限を回収する。 -/
lemma alternatingCellBoundaryLift_ι (m : ℕ) :
    alternatingCellBoundaryLift.{u} m ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.retractionStage m).ι =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingCellBoundary (m + 1)).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingCell (m + 1) := rfl

/-- 元の境界・元の前段階・元の全セルの貼付けの正方形は厳密に可換。 -/
lemma alternatingCellBoundaryLift_square (m : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingCellBoundary (m + 1)).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.retractionStageCell.{u} (m + 1) =
      alternatingCellBoundaryLift m ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.retractionStageMap (Nat.le_succ m) := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.retractionStage (m + 1)).ι).mp
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.retractionStageCell_ι, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.retractionStageMap_ι,
    alternatingCellBoundaryLift_ι]

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
