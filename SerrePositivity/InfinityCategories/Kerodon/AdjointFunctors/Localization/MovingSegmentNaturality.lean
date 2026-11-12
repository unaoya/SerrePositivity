module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingSegmentChains
public import Mathlib.CategoryTheory.CommSq

/-!
# 動く端点を持つ元の区間合成の自然性

概要：前後の端点が動く場合も、元の区間合成と全縦射の正方形を回収する。
方針：射列の自然変換と元の端点移送の正方形を合成する。
規約：元の全縦射を保持する。
使われ方：WordAction の区間合成を MovingDiagram に適用する。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingSegmentNaturality
open CategoryTheory Opposite

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word}
  {X Y X' Y' : C} {S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y} {T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X' Y'}

lemma point_transport (f : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom S T) {i j : Fin (w.length + 1)} (h : i = j) :
    eqToHom (congrArg S.vertex h) ≫ f.app j = f.app i ≫ eqToHom (congrArg T.vertex h) := by
  cases h
  simp

/-- 前向きの区間合成は元の両端の縦射と可換。 -/
lemma forward_map_comm (f : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom S T) (p q : Fin (w.length + 1)) (hpq : p ≤ q)
    (hd : ∀ i : Fin w.length, p.val ≤ i.val → i.val < q.val → w.direction i = .forward) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map .forward S p q hpq hd ≫ f.app q = f.app p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map .forward T p q hpq hd := by
  have hc := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingSegmentChains.forwardChainHom f p q hpq hd).naturality
    (homOfLE (show (0 : Fin (q.val - p.val + 1)) ≤ Fin.last _ from Fin.zero_le _))
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.chain .forward S p q hpq hd).hom ≫ f.app (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.index p q hpq (Fin.last _)) =
    f.app (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.index p q hpq 0) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.chain .forward T p q hpq hd).hom at hc
  exact (CommSq.horiz_comp ⟨point_transport f (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.index_zero p q hpq).symm⟩
    (CommSq.horiz_comp ⟨hc⟩ ⟨point_transport f (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.index_last p q hpq)⟩)).w

/-- 後ろ向きの区間合成も、元の圏の同じ両端の縦射と可換。 -/
lemma backward_map_comm (f : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom S T) (p q : Fin (w.length + 1)) (hpq : p ≤ q)
    (hd : ∀ i : Fin w.length, p.val ≤ i.val → i.val < q.val → w.direction i = .backward) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map .backward S p q hpq hd).unop ≫ f.app p =
      f.app q ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map .backward T p q hpq hd).unop := by
  have hc := congrArg Quiver.Hom.unop ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingSegmentChains.backwardChainHom f p q hpq hd).naturality
    (homOfLE (show (0 : Fin (q.val - p.val + 1)) ≤ Fin.last _ from Fin.zero_le _)))
  change f.app (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.index p q hpq (Fin.last _)) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.chain .backward T p q hpq hd).hom.unop =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.chain .backward S p q hpq hd).hom.unop ≫ f.app (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.index p q hpq 0) at hc
  have h₀ := point_transport f (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.index_last p q hpq).symm
  have h₁ := point_transport f (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.index_zero p q hpq)
  have h := (CommSq.horiz_comp ⟨h₀⟩ (CommSq.horiz_comp ⟨hc.symm⟩ ⟨h₁⟩)).w
  change (((eqToHom (congrArg (fun k => op (S.vertex k)) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.index_last p q hpq))).unop ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.chain .backward S p q hpq hd).hom.unop) ≫
      (eqToHom (congrArg (fun k => op (S.vertex k)) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.index_zero p q hpq).symm)).unop) ≫
        f.app p = f.app q ≫
      (((eqToHom (congrArg (fun k => op (T.vertex k)) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.index_last p q hpq))).unop ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.chain .backward T p q hpq hd).hom.unop) ≫
        (eqToHom (congrArg (fun k => op (T.vertex k)) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.index_zero p q hpq).symm)).unop)
  simpa only [eqToHom_unop, Category.assoc] using h

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingSegmentNaturality
