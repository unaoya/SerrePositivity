module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagForwardMovingToHom

/-!
# 元の前向き境界の縦射と固定 Hom の全単射

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
def forwardUnmovingApp {S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .forward w) X Y}
    {T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .forward w) X' Y} {f : X ⟶ X'}
    (h : S ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.forward T f) : ∀ j, S.vertex j ⟶ T.vertex j :=
  Fin.cases (eqToHom S.first ≫ f ≫ eqToHom T.first.symm) (fun j => h.app j.succ)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.forwardUnmovingApp export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (forwardUnmovingApp)


lemma forwardUnmovingApp_eq {S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .forward w) X Y}
    {T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .forward w) X' Y} {f : X ⟶ X'}
    (h : S ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.forward T f) (j : Fin (w.length + 2)) (hj : j ≠ 0) :
    forwardUnmovingApp h j = h.app j ≫ eqToHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFirstBoundaryMaps.vertex_eq T X j hj) := by
  cases j using Fin.cases with
  | zero => exact False.elim (hj rfl)
  | succ j => exact (Category.comp_id _).symm

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.forwardUnmovingApp_eq export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (forwardUnmovingApp_eq)


lemma forwardUnmovingTailComm {S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .forward w) X Y}
    {T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .forward w) X' Y} {f : X ⟶ X'}
    (h : S ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.forward T f) (i : Fin w.length) :
    S.arrow i.succ ≫ forwardUnmovingApp h ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .forward w).target i.succ) =
      forwardUnmovingApp h ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .forward w).source i.succ) ≫ T.arrow i.succ := by
  rw [forwardUnmovingApp_eq h _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFirstBoundaryMaps.target_succ_ne_zero .forward i),
    forwardUnmovingApp_eq h _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFirstBoundaryMaps.source_succ_ne_zero .forward i)]
  have hc := h.comm i.succ
  change S.arrow i.succ ≫ h.app _ = h.app _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.tailArrow T X i at hc
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.tailArrow, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.source, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.target, Category.assoc,
    eqToHom_trans_assoc, eqToHom_trans,
    eqToHom_refl, Category.id_comp, Category.comp_id] using
      congrArg (fun z => z ≫ eqToHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.vertex_target_succ T X i)) hc

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.forwardUnmovingTailComm export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (forwardUnmovingTailComm)


def forwardHomToMoving {S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .forward w) X Y}
    {T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .forward w) X' Y} {f : X ⟶ X'} (hf : W f)
    (h : S ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.forward T f) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BoundaryHom f S T where
  hom :=
    { app := forwardUnmovingApp h
      app_mem j := by
        cases j using Fin.cases with
        | zero => exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.transport_mem S.first T.first.symm f).mpr hf
        | succ j => exact h.app_mem j.succ
      comm i := by
        cases i using Fin.cases with
        | zero =>
          have hc : S.arrow (0 : Fin (w.length + 1)) ≫ h.app (0 : Fin (w.length + 1)).succ =
              h.app (0 : Fin (w.length + 2)) ≫ f ≫ eqToHom T.first.symm ≫
                T.arrow (0 : Fin (w.length + 1)) := h.comm (0 : Fin (w.length + 1))
          have hfirst : h.app (0 : Fin (w.length + 2)) = eqToHom S.first := h.first
          change S.arrow (0 : Fin (w.length + 1)) ≫ h.app (0 : Fin (w.length + 1)).succ =
            (eqToHom S.first ≫ f ≫ eqToHom T.first.symm) ≫ T.arrow (0 : Fin (w.length + 1))
          simpa only [hfirst, Category.assoc] using hc
        | succ i => exact forwardUnmovingTailComm h i }
  first := rfl
  last := h.last

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.forwardHomToMoving export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (forwardHomToMoving)


def forwardMovingEquiv (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .forward w) X Y)
    (T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .forward w) X' Y) (f : X ⟶ X') (hf : W f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BoundaryHom f S T ≃ (S ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.forward T f) where
  toFun := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardMovingToHom
  invFun := forwardHomToMoving hf
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

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.forwardMovingEquiv export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (forwardMovingEquiv)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
