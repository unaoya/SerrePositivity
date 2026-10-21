module

public import SerrePositivity.EInfinity.Hammock.ZigzagBoundaryHom

/-!
# 元の後向きの動く境界の縦射を固定 Hom へ移す

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
def backwardMovingApp {S : Zigzag W (Word.cons .backward w) X Y}
    {T : Zigzag W (Word.cons .backward w) X' Y} {f : X ⟶ X'} (hf : W f)
    (h : BoundaryHom f S T) : ∀ j, (backward S f hf).vertex j ⟶ T.vertex j :=
  Fin.cases (eqToHom T.first.symm) (fun j => h.hom.app j.succ)

lemma backwardMovingApp_eq {S : Zigzag W (Word.cons .backward w) X Y}
    {T : Zigzag W (Word.cons .backward w) X' Y} {f : X ⟶ X'} (hf : W f)
    (h : BoundaryHom f S T) (j : Fin (w.length + 2)) (hj : j ≠ 0) :
    backwardMovingApp hf h j = eqToHom (vertex_eq S X' j hj) ≫ h.hom.app j := by
  cases j using Fin.cases with
  | zero => exact False.elim (hj rfl)
  | succ j => exact (Category.id_comp _).symm

lemma backwardMovingTailComm {S : Zigzag W (Word.cons .backward w) X Y}
    {T : Zigzag W (Word.cons .backward w) X' Y} {f : X ⟶ X'} (hf : W f)
    (h : BoundaryHom f S T) (i : Fin w.length) :
    tailArrow S X' i ≫ backwardMovingApp hf h ((Word.cons .backward w).target i.succ) =
      backwardMovingApp hf h ((Word.cons .backward w).source i.succ) ≫ T.arrow i.succ := by
  unfold tailArrow
  rw [backwardMovingApp_eq hf h _ (target_succ_ne_zero .backward i),
    backwardMovingApp_eq hf h _ (source_succ_ne_zero .backward i)]
  simpa only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans,
    eqToHom_refl, Category.id_comp, Category.comp_id] using
      congrArg (fun z => eqToHom (vertex_source_succ S X' i) ≫ z) (h.hom.comm i.succ)

def backwardMovingToHom {S : Zigzag W (Word.cons .backward w) X Y}
    {T : Zigzag W (Word.cons .backward w) X' Y} {f : X ⟶ X'} (hf : W f)
    (h : BoundaryHom f S T) : backward S f hf ⟶ T where
  app := backwardMovingApp hf h
  app_mem j := by
    cases j using Fin.cases with
    | zero => exact Segment.eqToHom_mem T.first.symm
    | succ j => exact h.hom.app_mem j.succ
  first := rfl
  last := h.last
  comm i := by
    cases i using Fin.cases with
    | zero =>
      change (S.arrow (0 : Fin (w.length + 1)) ≫ eqToHom S.first ≫ f) ≫
        eqToHom T.first.symm =
          h.hom.app (0 : Fin (w.length + 1)).succ ≫ T.arrow (0 : Fin (w.length + 1))
      have hc : S.arrow (0 : Fin (w.length + 1)) ≫ h.hom.app (0 : Fin (w.length + 2)) =
          h.hom.app (0 : Fin (w.length + 1)).succ ≫ T.arrow (0 : Fin (w.length + 1)) :=
        h.hom.comm (0 : Fin (w.length + 1))
      simpa only [h.first, Category.assoc] using hc
    | succ i => exact backwardMovingTailComm hf h i

end SerrePositivity.EInfinity.Hammock.Zigzag.FirstBoundary
