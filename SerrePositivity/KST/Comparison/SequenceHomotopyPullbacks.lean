module

public import SerrePositivity.KST.Comparison.HomotopyPullbackPasting
public import SerrePositivity.KST.Comparison.KanReplacementSquares

/-!
# 順序列の隣接するホモトピー引き戻し

概要：縦射が Kan fibration なら、隣接する自然性の四角形から全ての遷移の四角形を得る。
方針：恒等射の場合と横の貼り合わせから自然数で帰納する。
規約：Segal 1974 Lemma 1.8。無限段階の結論は含めない。
使われ方：telescope の偶数・奇数への二射の仮定を隣接段から得る。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits

/--
概要：恒等の添字射の自然性の四角形は、縦射が Kan ならホモトピー引き戻しである。
方針：恒等の二辺を持つ厳密な引き戻しに Kan 判定を使う。
規約：添字の圏は任意。
使われ方：順序列の帰納の基底。
-/
theorem diagramArrow_id_homotopyPullback {D : Type v} [Category.{w} D]
    {F G : D ⥤ SSet.{u}} (α : F ⟶ G) (d : D)
    (hα : SSet.modelCategoryQuillen.J.rlp (α.app d)) :
    IsHomotopyPullback (naturalitySquare (diagramArrow (𝟙 d)) α) := by
  let : IsIso ((diagramArrow (𝟙 d)).app F) := by
    change IsIso (F.map (𝟙 d))
    rw [CategoryTheory.Functor.map_id]
    infer_instance
  let : IsIso ((diagramArrow (𝟙 d)).app G) := by
    change IsIso (G.map (𝟙 d))
    rw [CategoryTheory.Functor.map_id]
    infer_instance
  exact isHomotopyPullback_of_left_fibration
    (IsPullback.of_horiz_isIso (naturalitySquare (diagramArrow (𝟙 d)) α)) hα

/--
概要：隣接する自然性の四角形がホモトピー引き戻しなら、任意の遷移でも同じ性質が成り立つ。
方針：上端の段階について帰納し、中央の Kan fibration で横に貼り合わせる。
規約：順序列の各縦射の Kan 性を使う。
使われ方：telescope の辺の二つの端への射の四角形。
-/
theorem sequenceArrow_homotopyPullback_of_successors {F G : ℕ ⥤ SSet.{u}}
    (α : F ⟶ G) (hα : ∀ n, SSet.modelCategoryQuillen.J.rlp (α.app n))
    (h : ∀ n, IsHomotopyPullback
      (naturalitySquare (diagramArrow (homOfLE (Nat.le_succ n))) α))
    {n m : ℕ} (hnm : n ≤ m) :
    IsHomotopyPullback (naturalitySquare (diagramArrow (homOfLE hnm)) α) := by
  induction m, hnm using Nat.le_induction with
  | base => exact diagramArrow_id_homotopyPullback α n (hα n)
  | succ m hnm ih =>
    have hp := isHomotopyPullback_paste_horiz_of_middle_fibration
      (naturalitySquare (diagramArrow (homOfLE hnm)) α)
      (naturalitySquare (diagramArrow (homOfLE (Nat.le_succ m))) α) ih (h m) (hα m)
    simpa only [diagramArrow, ← Functor.map_comp] using hp

end SerrePositivity.KST.Comparison
