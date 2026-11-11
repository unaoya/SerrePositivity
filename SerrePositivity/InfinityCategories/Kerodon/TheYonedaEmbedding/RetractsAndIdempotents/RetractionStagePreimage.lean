module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.AlternatingOddRank
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.RetractionStageBoundary

/-!
概要：元の交互セルの前段階の逆像は、元の奇数頂点を全て含まないセル境界そのもの。
方針：元の射を保持する奇数位置数の比較を、元の各単体の像の表示へ適用する。
規約：元のセル・元の段階・元の全境界を使い、別の同値な複体で置き換えない。
使われ方：HTT 4.4.5.6 の元のセル貼付けの交わり。

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

/-- 元の交互セルの前段階の逆像は、元の全境界に含まれる。 -/
lemma alternatingCell_preimage_le_boundary (m : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.retractionStage m).preimage (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingCell.{u} (m + 1)) ≤
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingCellBoundary (m + 1) := by
  classical
  rintro ⟨⟨n⟩⟩ a ha
  change ∃ b, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingCell m).app (Opposite.op ⦋n⦌) b =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingCell (m + 1)).app (Opposite.op ⦋n⦌) a at ha
  obtain ⟨b, hb⟩ := ha
  by_contra hnot
  have hfull : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingSourceVertices (m + 1) ⊆
      Finset.univ.image (fun v : Fin (n + 1) ↦ a v) := by
    by_contra hn
    exact hnot ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.mem_missingFaceComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingSourceVertices (m + 1)) a).mpr hn)
  have hhit : ∀ i : Fin (m + 1), ∃ v : Fin (n + 1), (a v).val = 2 * i.val + 1 := by
    intro i
    let j : Fin (2 * (m + 1) + 1) := ⟨2 * i.val + 1, by have hi := i.isLt; omega⟩
    have hj : j ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingSourceVertices (m + 1) := by
      simp [_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingSourceVertices, j]
    obtain ⟨v, _, hv⟩ := Finset.mem_image.mp (hfull hj)
    exact ⟨v, congrArg Fin.val hv⟩
  have hle := _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingCell_odd_rank_le a b hb.symm hhit
  omega

/-- 元の交互セルの元の前段階への逆像は、元の全境界と厳密に等しい。 -/
lemma alternatingCell_stage_preimage (m : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.retractionStage m).preimage (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingCell.{u} (m + 1)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingCellBoundary (m + 1) :=
  le_antisymm (alternatingCell_preimage_le_boundary m) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingCellBoundary_le_preimage m)

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
