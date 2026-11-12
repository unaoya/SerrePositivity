module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FreeQuiverCoverZigzagVertical
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagPathIntervalValue

/-!
# 元の横列に沿う接頭ラベルの整合

概要：順向き・逆向きの元の各列が持ち上げ頂点のラベルを保つ。
方針：値の射列の合成則を使い、逆向きの列では同じ射で打ち消す。
規約：元の列とその元の向きを保持する。
使われ方：固定端点の zigzag 全体の持ち上げ。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q] (A : Q) {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {Y : Paths Q}
  (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (⊤ : MorphismProperty (Paths Q)) w ((Paths.of Q).obj A) Y)

lemma zigzagPrefix_edge (i : Fin w.length) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagPrefix A S i.castSucc ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.edge _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation_inverts_top S i =
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagPrefix A S i.succ := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagPrefix]
  rw [Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.path_map_adjacent, ← CategoryTheory.Functor.map_comp]
  congr 2

lemma zigzagPrefix_forward (i : Fin w.length) (hi : w.direction i = .forward) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagPrefix A S i.castSucc ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.arrow .forward S i hi) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagPrefix A S i.succ := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.edge_forward _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation_inverts_top S i hi]
  exact zigzagPrefix_edge A S i

lemma zigzagPrefix_backward (i : Fin w.length) (hi : w.direction i = .backward) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagPrefix A S i.succ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.arrow .backward S i hi).unop =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagPrefix A S i.castSucc := by
  have h := zigzagPrefix_edge A S i
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.edge_backward _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation_inverts_top S i hi] at h
  have hc := congrArg (fun p => p ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.backwardIso _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation_inverts_top S i hi).hom) h
  have hc' : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagPrefix A S i.castSucc = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagPrefix A S i.succ ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.backwardIso _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation_inverts_top S i hi).hom := by
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hc
  exact hc'.symm

lemma zigzagPrefix_arrow_transport (i : Fin w.length) (p q : Fin (w.length + 1))
    (hp : p = w.source i) (hq : w.target i = q)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagPrefix A S p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation.map
      (eqToHom (congrArg S.vertex hp) ≫ S.arrow i ≫ eqToHom (congrArg S.vertex hq)) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagPrefix A S q) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagPrefix A S (w.source i) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation.map (S.arrow i) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagPrefix A S (w.target i) := by
  subst p
  subst q
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using h

lemma zigzagPrefix_arrow (i : Fin w.length) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagPrefix A S (w.source i) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.positiveEvaluation.map (S.arrow i) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.zigzagPrefix A S (w.target i) := by
  cases hi : w.direction i with
  | forward =>
    apply zigzagPrefix_arrow_transport A S i i.castSucc i.succ
      (by simp [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.source, hi]) (by simp [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.target, hi])
    exact zigzagPrefix_forward A S i hi
  | backward =>
    apply zigzagPrefix_arrow_transport A S i i.succ i.castSucc
      (by simp [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.source, hi]) (by simp [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.target, hi])
    exact zigzagPrefix_backward A S i hi

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
