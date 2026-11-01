module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ForwardZigzagDiscrete
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.BackwardZigzagDiscrete
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagMovingHom

/-!
# 元の一列の評価と動く終点の縦射

概要：元の接合点の射を固定 Hom と元の一列の評価へ回収する。
方針：全列の正方形と元の端点移送を保つ。
規約：接合点の縦射を恒等射とは仮定しない。
使われ方：DK9.4・10.3の元の語の Grothendieck 分解。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory
variable {C : Type u} [Category.{u} C] {W : MorphismProperty C} {X Y Y' : C}
lemma ForwardZigzag.value_moving {S : Zigzag W (Word.single .forward) X Y}
    {T : Zigzag W (Word.single .forward) X Y'} (h : Zigzag.MovingHom S T)
    (hf : h.app (0 : Fin 2) = eqToHom (S.first.trans T.first.symm)) :
    value S ≫ (eqToHom S.last.symm ≫ h.app (1 : Fin 2) ≫ eqToHom T.last) = value T := by
  have hc : S.arrow (0 : Fin 1) ≫ h.app (1 : Fin 2) =
      h.app (0 : Fin 2) ≫ T.arrow (0 : Fin 1) := h.comm (0 : Fin 1)
  rw [hf] at hc
  simpa only [value, Category.assoc, eqToHom_trans_assoc, eqToHom_trans,
    eqToHom_refl, Category.id_comp] using
      congrArg (fun z => eqToHom S.first.symm ≫ z ≫ eqToHom T.last) hc
lemma BackwardZigzag.value_moving {S : Zigzag W (Word.single .backward) X Y}
    {T : Zigzag W (Word.single .backward) X Y'} (h : Zigzag.MovingHom S T)
    (hf : h.app (0 : Fin 2) = eqToHom (S.first.trans T.first.symm)) :
    (value S).val = (eqToHom S.last.symm ≫ h.app (1 : Fin 2) ≫ eqToHom T.last) ≫
      (value T).val := by
  have hc : S.arrow (0 : Fin 1) ≫ h.app (0 : Fin 2) =
      h.app (1 : Fin 2) ≫ T.arrow (0 : Fin 1) := h.comm (0 : Fin 1)
  rw [hf] at hc
  simpa only [value, Category.assoc, eqToHom_trans_assoc, eqToHom_trans,
    eqToHom_refl, Category.id_comp] using
      congrArg (fun z => eqToHom S.last.symm ≫ z ≫ eqToHom T.first) hc
end SerrePositivity.EInfinity.Hammock
