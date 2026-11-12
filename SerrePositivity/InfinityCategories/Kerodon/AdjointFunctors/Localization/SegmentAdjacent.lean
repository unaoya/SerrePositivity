module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SegmentParentComparison

/-!
# 一列の区間合成による元の射の回収

概要：一列だけを含む区間の合成は、同じ元の向き付き列の射に一致する。
方針：区間の両端の射を唯一の隣接射と比較し、構成した射列の隣接射を回収。
規約：元の圏または反対圏での等式であり、局所化を使わない。
使われ方：語の恒等写像による遷移が元の恒等関手になることの照合。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : C}

/-- 一列の区間の全列は、その同じ元の列。 -/
lemma adjacent_direction (d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) (i : Fin w.length) (hi : w.direction i = d)
    (j : Fin w.length) (hj : i.castSucc.val ≤ j.val) (hj' : j.val < i.succ.val) :
    w.direction j = d := by
  have h : j = i := Fin.ext (by change i.val ≤ j.val at hj; change j.val < i.val + 1 at hj'; omega)
  exact h ▸ hi

/-- 一列の区間合成は、元の同じ列の向きに応じた射。 -/
lemma map_adjacent (d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y) (i : Fin w.length)
    (hi : w.direction i = d) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map d S i.castSucc i.succ (Fin.castSucc_le_succ i) (adjacent_direction d i hi) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.arrow d S i hi := by
  let F := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.chain d S i.castSucc i.succ (Fin.castSucc_le_succ i) (adjacent_direction d i hi)
  have hn : i.succ.val - i.castSucc.val = 1 := by
    change i.val + 1 - i.val = 1
    omega
  have h₁ : HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.map d S i.castSucc i.succ (Fin.castSucc_le_succ i)
      (adjacent_direction d i hi)) F.hom := by
    change HEq (eqToHom _ ≫ F.hom ≫ eqToHom _) F.hom
    simp only [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
    rfl
  have h₂ : HEq F.hom (F.map' 0 1 (by omega) (by omega)) := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fin_map_heq F rfl
    apply Fin.ext
    exact hn
  have h₃ : HEq (F.map' 0 1 (by omega) (by omega)) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.arrow d S i hi) := by
    dsimp only [F, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Segment.chain]
    rw [ComposableArrows.mkOfObjOfMapSucc_map_succ _ _ 0 (by omega)]
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SegmentRestriction.arrow_heq
    apply Fin.ext
    rfl
  exact eq_of_heq (h₁.trans (h₂.trans h₃))

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
