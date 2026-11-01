module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagBackwardMovingToHom

/-!
# 元の後向き境界の縦射と固定 Hom の全単射

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
def backwardUnmovingApp {S : Zigzag W (Word.cons .backward w) X Y}
    {T : Zigzag W (Word.cons .backward w) X' Y} {f : X ⟶ X'} {hf : W f}
    (h : backward S f hf ⟶ T) : ∀ j, S.vertex j ⟶ T.vertex j :=
  Fin.cases (eqToHom S.first ≫ f ≫ eqToHom T.first.symm) (fun j => h.app j.succ)

lemma backwardUnmovingApp_eq {S : Zigzag W (Word.cons .backward w) X Y}
    {T : Zigzag W (Word.cons .backward w) X' Y} {f : X ⟶ X'} {hf : W f}
    (h : backward S f hf ⟶ T) (j : Fin (w.length + 2)) (hj : j ≠ 0) :
    backwardUnmovingApp h j = eqToHom (vertex_eq S X' j hj).symm ≫ h.app j := by
  cases j using Fin.cases with
  | zero => exact False.elim (hj rfl)
  | succ j => exact (Category.id_comp _).symm

lemma backwardUnmovingTailComm {S : Zigzag W (Word.cons .backward w) X Y}
    {T : Zigzag W (Word.cons .backward w) X' Y} {f : X ⟶ X'} {hf : W f}
    (h : backward S f hf ⟶ T) (i : Fin w.length) :
    S.arrow i.succ ≫ backwardUnmovingApp h ((Word.cons .backward w).target i.succ) =
      backwardUnmovingApp h ((Word.cons .backward w).source i.succ) ≫ T.arrow i.succ := by
  rw [backwardUnmovingApp_eq h _ (target_succ_ne_zero .backward i),
    backwardUnmovingApp_eq h _ (source_succ_ne_zero .backward i)]
  have hc := h.comm i.succ
  change tailArrow S X' i ≫ h.app _ = h.app _ ≫ T.arrow i.succ at hc
  simpa only [tailArrow, Word.source, Word.target, Category.assoc,
    eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl, Category.id_comp, Category.comp_id] using
      congrArg (fun z => eqToHom (vertex_source_succ S X' i).symm ≫ z) hc

def backwardHomToMoving {S : Zigzag W (Word.cons .backward w) X Y}
    {T : Zigzag W (Word.cons .backward w) X' Y} {f : X ⟶ X'} {hf : W f}
    (h : backward S f hf ⟶ T) : BoundaryHom f S T where
  hom :=
    { app := backwardUnmovingApp h
      app_mem j := by
        cases j using Fin.cases with
        | zero => exact (Direction.transport_mem S.first T.first.symm f).mpr hf
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

def backwardMovingEquiv (S : Zigzag W (Word.cons .backward w) X Y)
    (T : Zigzag W (Word.cons .backward w) X' Y) (f : X ⟶ X') (hf : W f) :
    BoundaryHom f S T ≃ (backward S f hf ⟶ T) where
  toFun := backwardMovingToHom hf
  invFun := backwardHomToMoving
  left_inv h := by
    apply BoundaryHom.ext
    apply MovingHom.ext
    intro j
    cases j using Fin.cases with
    | zero => exact h.first.symm
    | succ j => rfl
  right_inv h := by
    apply Zigzag.hom_ext
    intro j
    cases j using Fin.cases with
    | zero => exact h.first.symm
    | succ j => rfl
end SerrePositivity.EInfinity.Hammock.Zigzag.FirstBoundary
