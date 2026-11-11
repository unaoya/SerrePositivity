module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment

/-!
# 同方向列の合成と元の縦射の整合

概要：各列の元の可換正方形を、連続区間の合成射の正方形へ接続する。
方針：方向ごとに合成可能射列の自然変換を作り、両端で評価する。
規約：後ろ向きでは自然変換の向きも反転する。元の縦射を変更しない。
使われ方：語の写像による列の圧縮を全縦射上の関手にする。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SegmentNaturality
open CategoryTheory Opposite

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : C}
  {S T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y}

/-- 元の一列の正方形は、端点の等式による移送と可換。 -/
lemma square_transport (f : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Hom S T) (i : Fin w.length)
    (l r : Fin (w.length + 1)) (hl : l = w.source i) (hr : w.target i = r) :
    (eqToHom (congrArg S.vertex hl) ≫ S.arrow i ≫ eqToHom (congrArg S.vertex hr)) ≫
        f.app r =
      f.app l ≫ eqToHom (congrArg T.vertex hl) ≫ T.arrow i ≫
        eqToHom (congrArg T.vertex hr) := by
  subst l
  subst r
  simpa using f.comm i

lemma forward_arrow_comm (f : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Hom S T) (i : Fin w.length)
    (hi : w.direction i = .forward) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.arrow .forward S i hi ≫ f.app i.succ =
      f.app i.castSucc ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.arrow .forward T i hi :=
  square_transport f i _ _ (by simp [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.source, hi]) (by simp [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.target, hi])

lemma backward_arrow_comm (f : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Hom S T) (i : Fin w.length)
    (hi : w.direction i = .backward) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.arrow .backward S i hi).unop ≫ f.app i.castSucc =
      f.app i.succ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.arrow .backward T i hi).unop :=
  square_transport f i _ _ (by simp [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.source, hi]) (by simp [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.target, hi])

/-- 前向きの連続区間の合成可能射列の間の、元の全縦射。 -/
def forwardChainHom (f : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Hom S T) (p q : Fin (w.length + 1)) (hpq : p ≤ q)
    (hd : ∀ i : Fin w.length, p.val ≤ i.val → i.val < q.val → w.direction i = .forward) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.chain .forward S p q hpq hd ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.chain .forward T p q hpq hd :=
  ComposableArrows.homMk (fun k => f.app (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.index p q hpq k)) (by
    intro k hk
    dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.chain]
    rw [ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ k hk,
      ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ k hk]
    exact forward_arrow_comm f _ _)

/-- 後ろ向きの区間では、元の全縦射の反対射で自然変換の向きも反転。 -/
def backwardChainHom (f : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Hom S T) (p q : Fin (w.length + 1)) (hpq : p ≤ q)
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

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SegmentNaturality
