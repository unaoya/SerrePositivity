module

public import SerrePositivity.KST.Comparison.FatAttachmentSpan
public import SerrePositivity.KST.Comparison.FatBoundaryHomotopyPullback
public import SerrePositivity.KST.Comparison.SpanPushoutGluing

/-!
# 境界の比較から次の骨格への比較

概要：境界の付着の比較から、旧骨格と新しい行の次の骨格への比較を得る。
方針：右脚が単射な実際の付着の span へ Segal Lemma 1.7 を適用する。
規約：Segal 1974 Proposition 1.6 の一段階の骨格の帰納。
使われ方：全ての低い行の比較を次の骨格へ伸ばす。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits Opposite MonoidalCategory
open scoped Simplicial

/--
概要：次の骨格への包含は二重単体集合の射について自然。
方針：同じ元に同じ fat realization の射を適用することを計算する。
規約：元の部分対象への制限の等式。
使われ方：旧骨格から次の骨格への比較の四角形。
-/
@[reassoc] theorem fatSkeletonStep_map {F G : SimplexCategoryᵒᵖ ⥤ SSet.{u}}
    (α : F ⟶ G) (n : ℕ) :
    fatSkeletonStep F n ≫ fatSkeletonMap α (n + 1) =
      fatSkeletonMap α n ≫ fatSkeletonStep G n := rfl

/--
概要：境界の付着の比較から、旧骨格と新しい行の次の骨格への比較が従う。
方針：付着の左面と、積の厳密な引き戻しである右面から、pushout の各頂点を得る。
規約：新しい行の射の Kan 性だけを技術的条件に使う。
使われ方：有限骨格の帰納の一段階。
-/
theorem fatSkeleton_successor_homotopyPullback
    {F G : SimplexCategoryᵒᵖ ⥤ SSet.{u}} (α : F ⟶ G) (n : ℕ)
    (hKan : SSet.modelCategoryQuillen.J.rlp (α.app (op ⦋n + 1⦌)))
    (hboundary : IsHomotopyPullback (CommSq.mk (fatBoundaryAttachment_map α n))) :
    IsHomotopyPullback (CommSq.mk (fatSkeletonStep_map α n)) ∧
      IsHomotopyPullback (CommSq.mk (fatSkeletonRowOfLE_map α (le_refl (n + 1)))) := by
  have hL : IsHomotopyPullback
      (naturalitySquare (diagramArrow WalkingSpan.Hom.fst) (fatAttachmentSpanMap α n)) :=
    hboundary
  have hR : IsHomotopyPullback
      (naturalitySquare (diagramArrow WalkingSpan.Hom.snd) (fatAttachmentSpanMap α n)) := by
    exact isHomotopyPullback_of_left_fibration
      (cartesianTensorSquare_isPullback (α.app (op ⦋n + 1⦌)) (SSet.boundary (n + 1)).ι)
      (tensorRight_rlp _ hKan Δ[n + 1])
  have h := spanPushout_vertex_homotopyPullback (fatAttachmentSpanMap α n) hL hR
    (fatAttachmentCocone F n) (fatAttachmentCoconeIsColimit F n)
    (fatAttachmentCocone G n) (fatAttachmentCoconeIsColimit G n)
    (fatSkeletonMap α (n + 1)) (fatAttachmentCocone_map α n)
  exact ⟨h WalkingSpan.left, h WalkingSpan.right⟩

end SerrePositivity.KST.Comparison
