module

public import SerrePositivity.EInfinity.Hammock.ZigzagFirstBoundaryMaps
public import SerrePositivity.EInfinity.Hammock.ZigzagFirstBoundaryBackwardObjects
/-!
# 元の始点の後合成と全縦射への作用

概要：先頭 backward の語の始点への指定射の後合成を元の全縦射の関手にする。
方針：先頭の可換正方形と残りの元の全縦射の移送を照合する。
規約：同じ全縦弱同値と両端の恒等条件を保持する。
使われ方：DK9.3・10.3の元の先頭の向きによる共変係数。
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

def backwardMap {S T : Zigzag W (Word.cons .backward w) X Y}
    (f : X ⟶ X') (hf : W f) (h : S ⟶ T) : backward S f hf ⟶ backward T f hf where
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
      change (S.arrow (0 : Fin (w.length + 1)) ≫ eqToHom S.first ≫ f) ≫ (𝟙 X') =
        h.app (0 : Fin (w.length + 1)).succ ≫ T.arrow (0 : Fin (w.length + 1)) ≫ eqToHom T.first ≫ f
      have hc : S.arrow (0 : Fin (w.length + 1)) ≫ h.app (0 : Fin (w.length + 2)) =
          h.app (0 : Fin (w.length + 1)).succ ≫ T.arrow (0 : Fin (w.length + 1)) :=
        h.comm (0 : Fin (w.length + 1))
      rw [h.first] at hc
      simpa only [Category.assoc, Category.comp_id, eqToHom_trans_assoc, eqToHom_trans]
        using congrArg (fun z => z ≫ eqToHom T.first ≫ f) hc
    | succ i => exact tailComm h X' i

def backwardFunctor (f : X ⟶ X') (hf : W f) :
    Zigzag W (Word.cons .backward w) X Y ⥤ Zigzag W (Word.cons .backward w) X' Y where
  obj S := backward S f hf
  map h := backwardMap f hf h
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
