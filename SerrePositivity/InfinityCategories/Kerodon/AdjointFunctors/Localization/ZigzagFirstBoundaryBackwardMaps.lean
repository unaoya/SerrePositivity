module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFirstBoundaryMaps
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFirstBoundaryBackwardObjects
/-!
# 元の始点の後合成と全縦射への作用

概要：先頭 backward の語の始点への指定射の後合成を元の全縦射の関手にする。
方針：先頭の可換正方形と残りの元の全縦射の移送を照合する。
規約：同じ全縦弱同値と両端の恒等条件を保持する。
使われ方：DK9.3・10.3の元の先頭の向きによる共変係数。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFirstBoundaryBackwardMaps
open CategoryTheory
variable {C : Type u} [Category.{u} C] {W : MorphismProperty C} [W.IsMultiplicative]
  {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X X' Y : C}

def backwardMap {S T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .backward w) X Y}
    (f : X ⟶ X') (hf : W f) (h : S ⟶ T) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFirstBoundaryBackwardObjects.backward S f hf ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFirstBoundaryBackwardObjects.backward T f hf where
  app := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFirstBoundaryMaps.app h X'
  app_mem j := by
    cases j using Fin.cases with
    | zero => exact W.id_mem X'
    | succ j => exact h.app_mem j.succ
  first := rfl
  last := h.last
  comm i := by
    cases i using Fin.cases with
    | zero =>
      change (S.arrow (0 : Fin (w.length + 1)) ≫ eqToHom S.first ≫ f) ≫ (𝟙 X') =
        h.app (0 : Fin (w.length + 1)).succ ≫ T.arrow (0 : Fin (w.length + 1)) ≫ eqToHom T.first ≫ f
      have hc : S.arrow (0 : Fin (w.length + 1)) ≫ h.app (0 : Fin (w.length + 2)) =
          h.app (0 : Fin (w.length + 1)).succ ≫ T.arrow (0 : Fin (w.length + 1)) :=
        h.comm (0 : Fin (w.length + 1))
      rw [h.first] at hc
      simpa only [Category.assoc, Category.comp_id, eqToHom_trans_assoc, eqToHom_trans]
        using congrArg (fun z => z ≫ eqToHom T.first ≫ f) hc
    | succ i => exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFirstBoundaryMaps.tailComm h X' i

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.backwardMap export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFirstBoundaryBackwardMaps (backwardMap)


def backwardFunctor (f : X ⟶ X') (hf : W f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .backward w) X Y ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .backward w) X' Y where
  obj S := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFirstBoundaryBackwardObjects.backward S f hf
  map h := backwardMap f hf h
  map_id S := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.hom_ext
    intro j
    cases j using Fin.cases <;> rfl
  map_comp h l := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.hom_ext
    intro j
    cases j using Fin.cases with
    | zero =>
      change 𝟙 X' = (𝟙 X') ≫ 𝟙 X'
      simp only [Category.id_comp]
    | succ j => rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.backwardFunctor export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFirstBoundaryBackwardMaps (backwardFunctor)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFirstBoundaryBackwardMaps
