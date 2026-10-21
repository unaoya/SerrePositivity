module

public import SerrePositivity.EInfinity.Hammock.FreeQuiverCoverZigzagVertical
public import SerrePositivity.EInfinity.Hammock.ZigzagPathIntervalValue

/-!
# 元の横列に沿う接頭ラベルの整合

概要：順向き・逆向きの元の各列が持ち上げ頂点のラベルを保つ。
方針：値の射列の合成則を使い、逆向きの列では同じ射で打ち消す。
規約：元の列とその元の向きを保持する。
使われ方：固定端点の zigzag 全体の持ち上げ。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.FreeQuiverCover
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q] (A : Q) {w : Word} {Y : Paths Q}
  (S : Zigzag (⊤ : MorphismProperty (Paths Q)) w ((Paths.of Q).obj A) Y)

lemma zigzagPrefix_edge (i : Fin w.length) :
    zigzagPrefix A S i.castSucc ≫
      Zigzag.Value.edge positiveEvaluation positiveEvaluation_inverts_top S i =
        zigzagPrefix A S i.succ := by
  dsimp only [zigzagPrefix]
  rw [Category.assoc, ← Zigzag.Value.path_map_adjacent, ← CategoryTheory.Functor.map_comp]
  congr 2

lemma zigzagPrefix_forward (i : Fin w.length) (hi : w.direction i = .forward) :
    zigzagPrefix A S i.castSucc ≫ positiveEvaluation.map (Direction.arrow .forward S i hi) =
      zigzagPrefix A S i.succ := by
  rw [← Zigzag.Value.edge_forward positiveEvaluation positiveEvaluation_inverts_top S i hi]
  exact zigzagPrefix_edge A S i

lemma zigzagPrefix_backward (i : Fin w.length) (hi : w.direction i = .backward) :
    zigzagPrefix A S i.succ ≫ positiveEvaluation.map (Direction.arrow .backward S i hi).unop =
      zigzagPrefix A S i.castSucc := by
  have h := zigzagPrefix_edge A S i
  rw [Zigzag.Value.edge_backward positiveEvaluation positiveEvaluation_inverts_top S i hi] at h
  have hc := congrArg (fun p => p ≫
    (Zigzag.Value.backwardIso positiveEvaluation positiveEvaluation_inverts_top S i hi).hom) h
  have hc' : zigzagPrefix A S i.castSucc = zigzagPrefix A S i.succ ≫
      (Zigzag.Value.backwardIso positiveEvaluation positiveEvaluation_inverts_top S i hi).hom := by
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hc
  exact hc'.symm

lemma zigzagPrefix_arrow_transport (i : Fin w.length) (p q : Fin (w.length + 1))
    (hp : p = w.source i) (hq : w.target i = q)
    (h : zigzagPrefix A S p ≫ positiveEvaluation.map
      (eqToHom (congrArg S.vertex hp) ≫ S.arrow i ≫ eqToHom (congrArg S.vertex hq)) =
        zigzagPrefix A S q) :
    zigzagPrefix A S (w.source i) ≫ positiveEvaluation.map (S.arrow i) =
      zigzagPrefix A S (w.target i) := by
  subst p
  subst q
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using h

lemma zigzagPrefix_arrow (i : Fin w.length) :
    zigzagPrefix A S (w.source i) ≫ positiveEvaluation.map (S.arrow i) =
      zigzagPrefix A S (w.target i) := by
  cases hi : w.direction i with
  | forward =>
    apply zigzagPrefix_arrow_transport A S i i.castSucc i.succ
      (by simp [Word.source, hi]) (by simp [Word.target, hi])
    exact zigzagPrefix_forward A S i hi
  | backward =>
    apply zigzagPrefix_arrow_transport A S i i.succ i.castSucc
      (by simp [Word.source, hi]) (by simp [Word.target, hi])
    exact zigzagPrefix_backward A S i hi

end SerrePositivity.EInfinity.Hammock.FreeQuiverCover
