module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnRecovery
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SegmentUnits

/-!
# 同じ切断位置の間に挿入される元の恒等列

概要：切断位置が変わらない列の射を、元の頂点の等式による恒等列として回収する。
方針：空区間の合成を向きに応じた圏から戻す。
規約：単射性や元の対象の cofibrancy は要求しない。
使われ方：挿入恒等列の可換正方形による全縦射の回収。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : C}

lemma Segment.map_eqToHom_of_eq (d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y)
    (p q : Fin (a.length + 1)) (hpq : p ≤ q)
    (hd : ∀ i : Fin a.length, p.val ≤ i.val → i.val < q.val → a.direction i = d)
    (h : p = q) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map d S p q hpq hd = eqToHom (congrArg (fun i => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.vertex d (S.vertex i)) h) :=
  by cases h; exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.map_refl d S p hd

lemma Word.Hom.cut_source_target_of_eq (f : a ⟶ b) (j : Fin b.length)
    (h : f.cut j.castSucc = f.cut j.succ) : f.cut (b.source j) = f.cut (b.target j) := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.source _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.target
  cases b.direction j
  · exact h
  · exact h.symm

lemma WordAction.columnAux_eqToHom_of_eq {I : Type*} (V : I → C) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction)
    (p q : I) (h : V p = V q) (he : V (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.source d p q) = V (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.target d p q)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.columnAux V d p q (eqToHom (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.vertex d) h)) = eqToHom he := by
  cases d
  · rfl
  · change (eqToHom (C := Cᵒᵖ) (congrArg Opposite.op h)).unop = eqToHom he
    rw [eqToHom_unop]

lemma WordAction.column_eqToHom_of_cut_eq (f : a ⟶ b) (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y)
    (j : Fin b.length) (h : f.cut j.castSucc = f.cut j.succ)
    (he : f.cut (b.source j) = f.cut (b.target j)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.column f S j = eqToHom (congrArg S.vertex he) := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.column
  rw [Segment.map_eqToHom_of_eq _ _ _ _ _ _ h]
  exact WordAction.columnAux_eqToHom_of_eq (fun k => S.vertex (f.cut k))
    (b.direction j) j.castSucc j.succ (congrArg S.vertex h) (congrArg S.vertex he)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
