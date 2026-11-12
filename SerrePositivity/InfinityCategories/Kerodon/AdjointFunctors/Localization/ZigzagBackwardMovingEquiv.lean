module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagBackwardMovingToHom

/-!
# 元の後向き境界の縦射と固定 Hom の全単射

概要：元の接合点の指定射と全縦成分の対応を保つ。
方針：先頭成分だけを固定し、全列の正方形と元の端点移送を回収する。
規約：接合点の指定射を恒等射とは仮定しない。
使われ方：DK9.4・10.3の元の語の Grothendieck 分解。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory
variable {C : Type u} [Category.{u} C] {W : MorphismProperty C} [W.IsMultiplicative]
  {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X X' Y : C}
def backwardUnmovingApp {S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .backward w) X Y}
    {T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .backward w) X' Y} {f : X ⟶ X'} {hf : W f}
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFirstBoundaryBackwardObjects.backward S f hf ⟶ T) : ∀ j, S.vertex j ⟶ T.vertex j :=
  Fin.cases (eqToHom S.first ≫ f ≫ eqToHom T.first.symm) (fun j => h.app j.succ)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.backwardUnmovingApp export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (backwardUnmovingApp)


lemma backwardUnmovingApp_eq {S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .backward w) X Y}
    {T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .backward w) X' Y} {f : X ⟶ X'} {hf : W f}
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFirstBoundaryBackwardObjects.backward S f hf ⟶ T) (j : Fin (w.length + 2)) (hj : j ≠ 0) :
    backwardUnmovingApp h j = eqToHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFirstBoundaryMaps.vertex_eq S X' j hj).symm ≫ h.app j := by
  cases j using Fin.cases with
  | zero => exact False.elim (hj rfl)
  | succ j => exact (Category.id_comp _).symm

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.backwardUnmovingApp_eq export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (backwardUnmovingApp_eq)


lemma backwardUnmovingTailComm {S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .backward w) X Y}
    {T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .backward w) X' Y} {f : X ⟶ X'} {hf : W f}
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFirstBoundaryBackwardObjects.backward S f hf ⟶ T) (i : Fin w.length) :
    S.arrow i.succ ≫ backwardUnmovingApp h ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .backward w).target i.succ) =
      backwardUnmovingApp h ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .backward w).source i.succ) ≫ T.arrow i.succ := by
  rw [backwardUnmovingApp_eq h _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFirstBoundaryMaps.target_succ_ne_zero .backward i),
    backwardUnmovingApp_eq h _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFirstBoundaryMaps.source_succ_ne_zero .backward i)]
  have hc := h.comm i.succ
  change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.tailArrow S X' i ≫ h.app _ = h.app _ ≫ T.arrow i.succ at hc
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.tailArrow, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.source, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.target, Category.assoc,
    eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl, Category.id_comp, Category.comp_id] using
      congrArg (fun z => eqToHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.vertex_source_succ S X' i).symm ≫ z) hc

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.backwardUnmovingTailComm export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (backwardUnmovingTailComm)


def backwardHomToMoving {S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .backward w) X Y}
    {T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .backward w) X' Y} {f : X ⟶ X'} {hf : W f}
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFirstBoundaryBackwardObjects.backward S f hf ⟶ T) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BoundaryHom f S T where
  hom :=
    { app := backwardUnmovingApp h
      app_mem j := by
        cases j using Fin.cases with
        | zero => exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.transport_mem S.first T.first.symm f).mpr hf
        | succ j => exact h.app_mem j.succ
      comm i := by
        cases i using Fin.cases with
        | zero =>
          have hc : (S.arrow (0 : Fin (w.length + 1)) ≫ eqToHom S.first ≫ f) ≫
              h.app (0 : Fin (w.length + 2)) =
              h.app (0 : Fin (w.length + 1)).succ ≫ T.arrow (0 : Fin (w.length + 1)) :=
            h.comm (0 : Fin (w.length + 1))
          have hfirst : h.app (0 : Fin (w.length + 2)) = eqToHom T.first.symm := h.first
          change S.arrow (0 : Fin (w.length + 1)) ≫
            (eqToHom S.first ≫ f ≫ eqToHom T.first.symm) =
              h.app (0 : Fin (w.length + 1)).succ ≫ T.arrow (0 : Fin (w.length + 1))
          simpa only [hfirst, Category.assoc] using hc
        | succ i => exact backwardUnmovingTailComm h i }
  first := rfl
  last := h.last

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.backwardHomToMoving export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (backwardHomToMoving)


def backwardMovingEquiv (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .backward w) X Y)
    (T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .backward w) X' Y) (f : X ⟶ X') (hf : W f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BoundaryHom f S T ≃ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFirstBoundaryBackwardObjects.backward S f hf ⟶ T) where
  toFun := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.backwardMovingToHom hf
  invFun := backwardHomToMoving
  left_inv h := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BoundaryHom.ext
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.ext
    intro j
    cases j using Fin.cases with
    | zero => exact h.first.symm
    | succ j => rfl
  right_inv h := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.hom_ext
    intro j
    cases j using Fin.cases with
    | zero => exact h.first.symm
    | succ j => rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.backwardMovingEquiv export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (backwardMovingEquiv)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
