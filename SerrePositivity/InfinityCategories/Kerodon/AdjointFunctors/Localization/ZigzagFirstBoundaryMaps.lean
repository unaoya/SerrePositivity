module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFirstBoundaryObjects
/-!
# 元の始点の前合成と全縦射への作用

概要：先頭 forward の語の始点への前合成を元の全縦射の圏の関手にする。
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
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFirstBoundaryMaps
open CategoryTheory
variable {C : Type u} [Category.{u} C] {W : MorphismProperty C} [W.IsMultiplicative]
  {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X X' Y : C}

def app {d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction} {S T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons d w) X Y} (h : S ⟶ T) (X' : C) :
    ∀ j, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.vertex S X' j ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.vertex T X' j :=
  Fin.cases (𝟙 X') (fun i => h.app i.succ)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.app export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFirstBoundaryMaps (app)


lemma source_succ_ne_zero (d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) (i : Fin w.length) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons d w).source i.succ ≠ (0 : Fin (w.length + 2)) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.source, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons]
  simp only [Fin.cases_succ]
  cases w.direction i <;> simp [Fin.castSucc_succ]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.source_succ_ne_zero export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFirstBoundaryMaps (source_succ_ne_zero)


lemma target_succ_ne_zero (d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction) (i : Fin w.length) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons d w).target i.succ ≠ (0 : Fin (w.length + 2)) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.target, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons]
  simp only [Fin.cases_succ]
  cases w.direction i <;> simp [Fin.castSucc_succ]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.target_succ_ne_zero export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFirstBoundaryMaps (target_succ_ne_zero)


omit [W.IsMultiplicative] in
lemma vertex_eq {d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction} (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons d w) X Y) (X' : C)
    (j : Fin (w.length + 2)) (hj : j ≠ 0) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.vertex S X' j = S.vertex j := by
  cases j using Fin.cases with
  | zero => exact False.elim (hj rfl)
  | succ j => rfl

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.vertex_eq export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFirstBoundaryMaps (vertex_eq)


lemma app_eq {d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction} {S T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons d w) X Y} (h : S ⟶ T)
    (X' : C) (j : Fin (w.length + 2)) (hj : j ≠ 0) :
    app h X' j = eqToHom (vertex_eq S X' j hj) ≫ h.app j ≫
      eqToHom (vertex_eq T X' j hj).symm := by
  cases j using Fin.cases with
  | zero => exact False.elim (hj rfl)
  | succ j =>
    change h.app j.succ = (𝟙 _) ≫ h.app j.succ ≫ 𝟙 _
    simp only [Category.id_comp, Category.comp_id]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.app_eq export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFirstBoundaryMaps (app_eq)


lemma tailComm {d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction} {S T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons d w) X Y} (h : S ⟶ T)
    (X' : C) (i : Fin w.length) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.tailArrow S X' i ≫ app h X' ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons d w).target i.succ) =
      app h X' ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons d w).source i.succ) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.tailArrow T X' i := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.tailArrow
  rw [app_eq h X' _ (target_succ_ne_zero d i), app_eq h X' _ (source_succ_ne_zero d i)]
  simpa only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans,
    eqToHom_refl, Category.id_comp] using
      congrArg (fun z => eqToHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.vertex_source_succ S X' i) ≫ z ≫
        eqToHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.vertex_target_succ T X' i).symm) (h.comm i.succ)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.tailComm export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFirstBoundaryMaps (tailComm)


def forwardMap {S T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .forward w) X Y} (f : X' ⟶ X) (h : S ⟶ T) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.forward S f ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.forward T f where
  app := app h X'
  app_mem j := by
    cases j using Fin.cases with
    | zero => exact W.id_mem X'
    | succ j => exact h.app_mem j.succ
  first := rfl
  last := h.last
  comm i := by
    cases i using Fin.cases with
    | zero =>
      change (f ≫ eqToHom S.first.symm ≫ S.arrow (0 : Fin (w.length + 1))) ≫
          h.app (0 : Fin (w.length + 1)).succ =
        (𝟙 X') ≫ f ≫ eqToHom T.first.symm ≫ T.arrow (0 : Fin (w.length + 1))
      have hc : S.arrow (0 : Fin (w.length + 1)) ≫ h.app (0 : Fin (w.length + 1)).succ =
          h.app (0 : Fin (w.length + 2)) ≫ T.arrow (0 : Fin (w.length + 1)) :=
        h.comm (0 : Fin (w.length + 1))
      rw [h.first] at hc
      simpa only [Category.assoc, Category.id_comp, eqToHom_trans_assoc, eqToHom_trans]
        using congrArg (fun z => f ≫ eqToHom S.first.symm ≫ z) hc
    | succ i => exact tailComm h X' i

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.forwardMap export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFirstBoundaryMaps (forwardMap)


def forwardFunctor (f : X' ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .forward w) X Y ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .forward w) X' Y where
  obj S := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.forward S f
  map h := forwardMap f h
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

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.FirstBoundary.forwardFunctor export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFirstBoundaryMaps (forwardFunctor)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagFirstBoundaryMaps
