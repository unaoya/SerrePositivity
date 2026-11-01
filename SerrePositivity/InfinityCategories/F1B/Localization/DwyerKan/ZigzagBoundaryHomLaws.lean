module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagBoundaryHom

/-!
# 元の動く接合点の縦射の恒等と合成

概要：元の接合点の射を固定 Hom と元の一列の評価へ回収する。
方針：全列の正方形と元の端点移送を保つ。
規約：接合点の縦射を恒等射とは仮定しない。
使われ方：DK9.4・10.3の元の語の Grothendieck 分解。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.EInfinity.Hammock.Zigzag.FirstBoundary.BoundaryHom
open CategoryTheory
variable {C : Type u} [Category.{u} C] {W : MorphismProperty C} [W.IsMultiplicative]
  {w : Word} {d : Direction} {X X' X'' Y : C}
  {S : Zigzag W (Word.cons d w) X Y} {T : Zigzag W (Word.cons d w) X' Y}
  {U : Zigzag W (Word.cons d w) X'' Y}
  {f : X ⟶ X'} {g : X' ⟶ X''}
def ofMoving (h : MovingHom S T) (hf : HEq (h.app 0) f)
    (hl : HEq (h.app (Fin.last (Word.cons d w).length)) (𝟙 Y)) : BoundaryHom f S T where
  hom := h
  first := (conj_eqToHom_iff_heq _ _ S.first T.first).mpr hf
  last := h.last_of_heq_id hl

def id (S : Zigzag W (Word.cons d w) X Y) : BoundaryHom (𝟙 X) S S :=
  ofMoving (MovingHom.id S) (MovingHom.id_first S) (MovingHom.id_last S)

def comp (h : BoundaryHom f S T) (k : BoundaryHom g T U) : BoundaryHom (f ≫ g) S U where
  hom := h.hom.comp k.hom
  first := by
    change h.hom.app 0 ≫ k.hom.app 0 = _
    simp only [h.first, k.first, Category.assoc, eqToHom_trans_assoc,
      eqToHom_refl, Category.id_comp]
  last := by
    change h.hom.app _ ≫ k.hom.app _ = _
    simp only [h.last, k.last, eqToHom_trans]

lemma id_app (S : Zigzag W (Word.cons d w) X Y)
    (j : Fin ((Word.cons d w).length + 1)) : (id S).hom.app j = 𝟙 _ := rfl
lemma comp_app (h : BoundaryHom f S T) (k : BoundaryHom g T U)
    (j : Fin ((Word.cons d w).length + 1)) :
    (comp h k).hom.app j = h.hom.app j ≫ k.hom.app j := rfl
end SerrePositivity.EInfinity.Hammock.Zigzag.FirstBoundary.BoundaryHom
