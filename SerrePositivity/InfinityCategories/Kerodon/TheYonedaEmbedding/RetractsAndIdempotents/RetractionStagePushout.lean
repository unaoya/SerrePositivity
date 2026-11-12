module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.AlternatingCellKernel
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.RetractionStagePreimage
public import Mathlib.CategoryTheory.Limits.Types.Pushouts
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono

/-!
概要：元の Ret の隣接段階の可換正方形は、元の全セルを貼る実際の pushout。
方針：元の逆像境界の等式と、境界外の元の単体の一意性を各次数で使用する。
規約：元の段階・元のセル・元の全境界への写像を保持する。
使われ方：HTT 4.4.5.6 の Ret(m) から Ret(m+1) への貼付け。

対応節は Kerodon 8.5（Tag 03Y9）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-- 元の段階の構造射は、元の部分複体の単射な包含。 -/
instance retractionStageMap_mono {m M : ℕ} (h : m ≤ M) : Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.retractionStageMap.{u} h) :=
  inferInstanceAs (Mono (Subcomplex.homOfLE (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.retractionStage_mono h)))

/-- 元の全セルから元の像の段階への制限は、各次数で全射。 -/
lemma retractionStageCell_app_surjective (m n : ℕ) :
    Function.Surjective ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.retractionStageCell.{u} m).app (Opposite.op ⦋n⦌)) := by
  intro x
  obtain ⟨a, ha⟩ := x.property
  exact ⟨a, Subtype.ext ha⟩

/-- 元の隣接段階の正方形は、元の逆像境界の等式により各次数で pullback。 -/
lemma retractionStage_isPullback_app (m n : ℕ) :
    IsPullback ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingCellBoundaryLift.{u} m).app (Opposite.op ⦋n⦌))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingCellBoundary (m + 1)).ι.app (Opposite.op ⦋n⦌))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.retractionStageMap (Nat.le_succ m)).app (Opposite.op ⦋n⦌))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.retractionStageCell (m + 1)).app (Opposite.op ⦋n⦌)) := by
  apply (Types.isPullback_iff _ _ _ _).mpr
  refine ⟨?_, ?_, ?_⟩
  · exact congrArg (fun f ↦ f.app (Opposite.op ⦋n⦌))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingCellBoundaryLift_square.{u} m).symm
  · intro x y h
    exact Subtype.ext h.2
  · intro x y h
    have hv := congrArg Subtype.val h
    have hy : y ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingCellBoundary (m + 1)).obj (Opposite.op ⦋n⦌) := by
      rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingCell_stage_preimage m]
      change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingCell (m + 1)).app (Opposite.op ⦋n⦌) y ∈
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.retractionStage m).obj (Opposite.op ⦋n⦌)
      change x.val = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingCell (m + 1)).app (Opposite.op ⦋n⦌) y at hv
      rw [← hv]
      exact x.property
    refine ⟨⟨y, hy⟩, ?_, rfl⟩
    apply Subtype.ext
    exact hv.symm

/-- 元の隣接段階の正方形は、元のセルの核の分類により各次数で pushout。 -/
lemma retractionStage_isPushout_app (m n : ℕ) :
    IsPushout ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingCellBoundaryLift.{u} m).app (Opposite.op ⦋n⦌))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingCellBoundary (m + 1)).ι.app (Opposite.op ⦋n⦌))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.retractionStageMap (Nat.le_succ m)).app (Opposite.op ⦋n⦌))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.retractionStageCell (m + 1)).app (Opposite.op ⦋n⦌)) := by
  apply Types.isPushout_of_isPullback_of_mono' (retractionStage_isPullback_app.{u} m n)
  · apply Set.eq_univ_of_forall
    intro x
    exact Or.inr (retractionStageCell_app_surjective.{u} (m + 1) n x)
  · intro x y hx _hy h
    have hv := congrArg Subtype.val h
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingCell (m + 1)).app (Opposite.op ⦋n⦌) x =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingCell (m + 1)).app (Opposite.op ⦋n⦌) y at hv
    rcases _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingCell_kernel x y hv with he | ⟨hxB, _⟩
    · exact he
    · exact False.elim (hx ⟨⟨x, hxB⟩, rfl⟩)

/-- 元の隣接段階は、元の全境界から元の全セルを貼る実際の単体集合の pushout。 -/
lemma retractionStage_isPushout (m : ℕ) :
    IsPushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingCellBoundaryLift.{u} m) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingCellBoundary (m + 1)).ι
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.retractionStageMap (Nat.le_succ m)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.retractionStageCell (m + 1)) where
  w := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingCellBoundaryLift_square m).symm
  isColimit' := ⟨evaluationJointlyReflectsColimits _ (fun n ↦
    (PushoutCocone.isColimitMapCoconeEquiv _ _).symm (by
      rcases n with ⟨⟨d⟩⟩
      exact (retractionStage_isPushout_app.{u} m d).isColimit))⟩

/-- 元の Ret(1) 以後の各段階の元の包含は、元の境界を貼ることにより inner anodyne。 -/
lemma retractionStageMap_innerAnodyne (m : ℕ) (hm : 1 ≤ m) :
    innerAnodyneExtensions (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.retractionStageMap.{u} (Nat.le_succ m)) :=
  innerAnodyneExtensions.of_isPushout (retractionStage_isPushout.{u} m)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.alternatingCellBoundary_innerAnodyne (m + 1) (by omega))

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents
