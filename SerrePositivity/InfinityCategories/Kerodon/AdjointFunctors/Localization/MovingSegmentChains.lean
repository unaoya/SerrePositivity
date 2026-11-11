module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingHomSquareTransport

/-!
# 動く端点の元の全縦射による区間射列の自然変換

概要：動く端点の全縦射を、元の同方向区間の合成可能射列の間へ移す。
方針：元の各正方形を方向ごとに射列へ束ねる。
規約：端点の縦射を恒等射と仮定しない。
使われ方：局所の三列 collapse を前後の全語の図式に移す。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingSegmentChains
open CategoryTheory Opposite

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word}
  {X Y X' Y' : C} {S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y} {T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X' Y'}

lemma forward_arrow_comm (f : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom S T) (i : Fin w.length)
    (hi : w.direction i = .forward) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.arrow .forward S i hi ≫ f.app i.succ =
      f.app i.castSucc ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.arrow .forward T i hi :=
  f.square_transport i _ _ (by simp [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.source, hi]) (by simp [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.target, hi])

lemma backward_arrow_comm (f : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom S T) (i : Fin w.length)
    (hi : w.direction i = .backward) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.arrow .backward S i hi).unop ≫ f.app i.castSucc =
      f.app i.succ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.arrow .backward T i hi).unop :=
  f.square_transport i _ _ (by simp [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.source, hi]) (by simp [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.target, hi])

/-- 前向きの連続区間の合成可能射列の間の、元の全縦射。 -/
def forwardChainHom (f : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom S T) (p q : Fin (w.length + 1)) (hpq : p ≤ q)
    (hd : ∀ i : Fin w.length, p.val ≤ i.val → i.val < q.val → w.direction i = .forward) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.chain .forward S p q hpq hd ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.chain .forward T p q hpq hd :=
  ComposableArrows.homMk (fun k => f.app (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.index p q hpq k)) (by
    intro k hk
    dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.chain]
    rw [ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ k hk,
      ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ k hk]
    exact forward_arrow_comm f _ _)

/-- 後ろ向きの区間では、元の全縦射の反対射で自然変換の向きも反転。 -/
def backwardChainHom (f : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom S T) (p q : Fin (w.length + 1)) (hpq : p ≤ q)
    (hd : ∀ i : Fin w.length, p.val ≤ i.val → i.val < q.val → w.direction i = .backward) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.chain .backward T p q hpq hd ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.chain .backward S p q hpq hd :=
  ComposableArrows.homMk (fun k => (f.app (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.index p q hpq k)).op) (by
    intro k hk
    dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.chain]
    rw [ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ k hk,
      ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ k hk]
    apply Quiver.Hom.unop_inj
    let i : Fin w.length := ⟨p.val + k, by have := q.isLt; omega⟩
    have hi := hd i (by dsimp [i]; omega) (by dsimp [i]; omega)
    change f.app i.succ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.arrow .backward T i hi).unop =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.arrow .backward S i hi).unop ≫ f.app i.castSucc
    exact (backward_arrow_comm f i hi).symm)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingSegmentChains
