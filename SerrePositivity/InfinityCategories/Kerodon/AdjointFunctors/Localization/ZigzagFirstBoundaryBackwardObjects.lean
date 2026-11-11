module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFirstBoundaryObjects
/-!
# 先頭 backward の元の指定列への後合成

概要：指定射による始点の後合成を元の全頂点・全列で構成する。
方針：始点の成分だけを恒等射とし、残りの元の全射と可換正方形を保持する。
規約：元の指定条件・両端条件と全射列の関手則を保持する。
使われ方：DK9.3・10.3・5.7の元の固定語の端点 variance。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFirstBoundaryBackwardObjects
open CategoryTheory
variable {C : Type u} [Category.{u} C] {W : MorphismProperty C} {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X X' Y : C}
def backwardArrow (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .backward w) X Y) (f : X ⟶ X') :
    ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.vertex S X' ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .backward w).source i) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.vertex S X' ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .backward w).target i) :=
  Fin.cases (S.arrow (0 : Fin (w.length + 1)) ≫ eqToHom S.first ≫ f) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.tailArrow S X')

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.backwardArrow export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFirstBoundaryBackwardObjects (backwardArrow)


variable [W.IsMultiplicative]
def backward (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .backward w) X Y) (f : X ⟶ X') (hf : W f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .backward w) X' Y where
  vertex := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.vertex S X'
  first := rfl
  last := S.last
  arrow := backwardArrow S f
  backward_mem i hi := by
    cases i using Fin.cases with
    | zero =>
      change W (S.arrow (0 : Fin (w.length + 1)) ≫ eqToHom S.first ≫ f)
      have hS : W (S.arrow (0 : Fin (w.length + 1)) ≫ eqToHom S.first) := by
        simpa only [eqToHom_refl, Category.id_comp] using
          (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.transport_mem rfl S.first (S.arrow (0 : Fin (w.length + 1)))).mpr
            (S.backward_mem (0 : Fin (w.length + 1)) rfl)
      simpa only [Category.assoc] using
        W.comp_mem (S.arrow (0 : Fin (w.length + 1)) ≫ eqToHom S.first) f hS hf
    | succ i =>
      change W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.tailArrow S X' i)
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.transport_mem _ _ _).2 (S.backward_mem i.succ hi)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.backward export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFirstBoundaryBackwardObjects (backward)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFirstBoundaryBackwardObjects
