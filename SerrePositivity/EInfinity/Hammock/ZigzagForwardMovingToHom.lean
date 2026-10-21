module

public import SerrePositivity.EInfinity.Hammock.ZigzagBoundaryHom

/-!
# 元の前向きの動く境界の縦射を固定 Hom へ移す

概要：元の接合点の指定射と全縦成分の対応を保つ。
方針：先頭成分だけを固定し、全列の正方形と元の端点移送を回収する。
規約：接合点の指定射を恒等射とは仮定しない。
使われ方：DK9.4・10.3の元の語の Grothendieck 分解。
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
def forwardMovingApp {S : Zigzag W (Word.cons .forward w) X Y}
    {T : Zigzag W (Word.cons .forward w) X' Y} {f : X ⟶ X'}
    (h : BoundaryHom f S T) : ∀ j, S.vertex j ⟶ (forward T f).vertex j :=
  Fin.cases (eqToHom S.first) (fun j => h.hom.app j.succ)

omit [W.IsMultiplicative] in
lemma forwardMovingApp_eq {S : Zigzag W (Word.cons .forward w) X Y}
    {T : Zigzag W (Word.cons .forward w) X' Y} {f : X ⟶ X'}
    (h : BoundaryHom f S T) (j : Fin (w.length + 2)) (hj : j ≠ 0) :
    forwardMovingApp h j = h.hom.app j ≫ eqToHom (vertex_eq T X j hj).symm := by
  cases j using Fin.cases with
  | zero => exact False.elim (hj rfl)
  | succ j => exact (Category.comp_id _).symm

omit [W.IsMultiplicative] in
lemma forwardMovingTailComm {S : Zigzag W (Word.cons .forward w) X Y}
    {T : Zigzag W (Word.cons .forward w) X' Y} {f : X ⟶ X'}
    (h : BoundaryHom f S T) (i : Fin w.length) :
    S.arrow i.succ ≫ forwardMovingApp h ((Word.cons .forward w).target i.succ) =
      forwardMovingApp h ((Word.cons .forward w).source i.succ) ≫ tailArrow T X i := by
  unfold tailArrow
  rw [forwardMovingApp_eq h _ (target_succ_ne_zero .forward i),
    forwardMovingApp_eq h _ (source_succ_ne_zero .forward i)]
  simpa only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans,
    eqToHom_refl, Category.id_comp, Category.comp_id] using
      congrArg (fun z => z ≫ eqToHom (vertex_target_succ T X i).symm) (h.hom.comm i.succ)

def forwardMovingToHom {S : Zigzag W (Word.cons .forward w) X Y}
    {T : Zigzag W (Word.cons .forward w) X' Y} {f : X ⟶ X'}
    (h : BoundaryHom f S T) : S ⟶ forward T f where
  app := forwardMovingApp h
  app_mem j := by
    cases j using Fin.cases with
    | zero => simpa only [forwardMovingApp, Fin.cases_zero] using Segment.eqToHom_mem S.first
    | succ j => exact h.hom.app_mem j.succ
  first := rfl
  last := h.last
  comm i := by
    cases i using Fin.cases with
    | zero =>
      change S.arrow (0 : Fin (w.length + 1)) ≫ h.hom.app (0 : Fin (w.length + 1)).succ =
        eqToHom S.first ≫ f ≫ eqToHom T.first.symm ≫ T.arrow (0 : Fin (w.length + 1))
      have hc : S.arrow (0 : Fin (w.length + 1)) ≫ h.hom.app (0 : Fin (w.length + 1)).succ =
          h.hom.app (0 : Fin (w.length + 2)) ≫ T.arrow (0 : Fin (w.length + 1)) :=
        h.hom.comm (0 : Fin (w.length + 1))
      simpa only [h.first, Category.assoc] using hc
    | succ i => exact forwardMovingTailComm h i

end SerrePositivity.EInfinity.Hammock.Zigzag.FirstBoundary
