module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagFirstBoundaryObjects
/-!
# 元の始点の前合成と全縦射への作用

概要：先頭 forward の語の始点への前合成を元の全縦射の圏の関手にする。
方針：始点の成分だけを恒等射とし、残りの元の全射と可換正方形を保持する。
規約：元の指定条件・両端条件と全射列の関手則を保持する。
使われ方：DK9.3・10.3・5.7の元の固定語の端点 variance。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Hammock.Zigzag.FirstBoundary
open CategoryTheory
variable {C : Type u} [Category.{u} C] {W : MorphismProperty C} [W.IsMultiplicative]
  {w : Word} {X X' Y : C}

def app {d : Direction} {S T : Zigzag W (Word.cons d w) X Y} (h : S ⟶ T) (X' : C) :
    ∀ j, vertex S X' j ⟶ vertex T X' j :=
  Fin.cases (𝟙 X') (fun i => h.app i.succ)

lemma source_succ_ne_zero (d : Direction) (i : Fin w.length) :
    (Word.cons d w).source i.succ ≠ (0 : Fin (w.length + 2)) := by
  dsimp only [Word.source, Word.cons]
  simp only [Fin.cases_succ]
  cases w.direction i <;> simp [Fin.castSucc_succ]

lemma target_succ_ne_zero (d : Direction) (i : Fin w.length) :
    (Word.cons d w).target i.succ ≠ (0 : Fin (w.length + 2)) := by
  dsimp only [Word.target, Word.cons]
  simp only [Fin.cases_succ]
  cases w.direction i <;> simp [Fin.castSucc_succ]

omit [W.IsMultiplicative] in
lemma vertex_eq {d : Direction} (S : Zigzag W (Word.cons d w) X Y) (X' : C)
    (j : Fin (w.length + 2)) (hj : j ≠ 0) : vertex S X' j = S.vertex j := by
  cases j using Fin.cases with
  | zero => exact False.elim (hj rfl)
  | succ j => rfl

lemma app_eq {d : Direction} {S T : Zigzag W (Word.cons d w) X Y} (h : S ⟶ T)
    (X' : C) (j : Fin (w.length + 2)) (hj : j ≠ 0) :
    app h X' j = eqToHom (vertex_eq S X' j hj) ≫ h.app j ≫
      eqToHom (vertex_eq T X' j hj).symm := by
  cases j using Fin.cases with
  | zero => exact False.elim (hj rfl)
  | succ j =>
    change h.app j.succ = (𝟙 _) ≫ h.app j.succ ≫ 𝟙 _
    simp only [Category.id_comp, Category.comp_id]

lemma tailComm {d : Direction} {S T : Zigzag W (Word.cons d w) X Y} (h : S ⟶ T)
    (X' : C) (i : Fin w.length) :
    tailArrow S X' i ≫ app h X' ((Word.cons d w).target i.succ) =
      app h X' ((Word.cons d w).source i.succ) ≫ tailArrow T X' i := by
  unfold tailArrow
  rw [app_eq h X' _ (target_succ_ne_zero d i), app_eq h X' _ (source_succ_ne_zero d i)]
  simpa only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans,
    eqToHom_refl, Category.id_comp] using
      congrArg (fun z => eqToHom (vertex_source_succ S X' i) ≫ z ≫
        eqToHom (vertex_target_succ T X' i).symm) (h.comm i.succ)

def forwardMap {S T : Zigzag W (Word.cons .forward w) X Y} (f : X' ⟶ X) (h : S ⟶ T) :
    forward S f ⟶ forward T f where
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

def forwardFunctor (f : X' ⟶ X) :
    Zigzag W (Word.cons .forward w) X Y ⥤ Zigzag W (Word.cons .forward w) X' Y where
  obj S := forward S f
  map h := forwardMap f h
  map_id S := by
    apply Zigzag.hom_ext
    intro j
    cases j using Fin.cases <;> rfl
  map_comp h l := by
    apply Zigzag.hom_ext
    intro j
    cases j using Fin.cases with
    | zero =>
      change 𝟙 X' = (𝟙 X') ≫ 𝟙 X'
      simp only [Category.id_comp]
    | succ j => rfl
end SerrePositivity.EInfinity.Hammock.Zigzag.FirstBoundary
