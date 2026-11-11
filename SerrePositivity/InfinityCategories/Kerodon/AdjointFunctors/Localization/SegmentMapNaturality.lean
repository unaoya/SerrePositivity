module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SegmentNaturality
public import Mathlib.CategoryTheory.CommSq

/-!
# 元の端点を持つ区間合成の自然性

概要：端点の等式も含めた区間合成は元の縦射の正方形と可換。
方針：始点の移送・合成可能射列・終点の移送の三つの可換正方形を合成する。
規約：後ろ向きの射は元の圏で戻し、元の端点の縦射を保持する。
使われ方：語の単調写像の fiber 合成による zigzag の関手。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SegmentMapNaturality
open CategoryTheory Opposite

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : C}
  {S T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y}

/-- 頂点の等式による移送は同じ元の縦射と可換。 -/
lemma point_transport (f : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Hom S T) {i j : Fin (w.length + 1)} (h : i = j) :
    eqToHom (congrArg S.vertex h) ≫ f.app j = f.app i ≫ eqToHom (congrArg T.vertex h) := by
  cases h
  simp

/-- 前向きの区間合成は元の両端の縦射と可換。 -/
lemma forward_map_comm (f : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Hom S T) (p q : Fin (w.length + 1)) (hpq : p ≤ q)
    (hd : ∀ i : Fin w.length, p.val ≤ i.val → i.val < q.val → w.direction i = .forward) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map .forward S p q hpq hd ≫ f.app q = f.app p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map .forward T p q hpq hd := by
  have hc := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SegmentNaturality.forwardChainHom f p q hpq hd).naturality
    (homOfLE (show (0 : Fin (q.val - p.val + 1)) ≤ Fin.last _ from Fin.zero_le _))
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.chain .forward S p q hpq hd).hom ≫ f.app (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.index p q hpq (Fin.last _)) =
    f.app (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.index p q hpq 0) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.chain .forward T p q hpq hd).hom at hc
  exact (CommSq.horiz_comp ⟨point_transport f (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.index_zero p q hpq).symm⟩
    (CommSq.horiz_comp ⟨hc⟩ ⟨point_transport f (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.index_last p q hpq)⟩)).w

/-- 後ろ向きの区間合成も、元の圏の同じ両端の縦射と可換。 -/
lemma backward_map_comm (f : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Hom S T) (p q : Fin (w.length + 1)) (hpq : p ≤ q)
    (hd : ∀ i : Fin w.length, p.val ≤ i.val → i.val < q.val → w.direction i = .backward) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map .backward S p q hpq hd).unop ≫ f.app p =
      f.app q ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map .backward T p q hpq hd).unop := by
  have hc := congrArg Quiver.Hom.unop ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SegmentNaturality.backwardChainHom f p q hpq hd).naturality
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

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SegmentMapNaturality
