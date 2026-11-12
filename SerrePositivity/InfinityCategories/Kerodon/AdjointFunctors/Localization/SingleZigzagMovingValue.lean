module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzagDiscrete
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzagDiscrete
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingHom

/-!
# 元の一列の評価と動く終点の縦射

概要：元の接合点の射を固定 Hom と元の一列の評価へ回収する。
方針：全列の正方形と元の端点移送を保つ。
規約：接合点の縦射を恒等射とは仮定しない。
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
variable {C : Type u} [Category.{u} C] {W : MorphismProperty C} {X Y Y' : C}
lemma ForwardZigzag.value_moving {S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) X Y}
    {T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .forward) X Y'} (h : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom S T)
    (hf : h.app (0 : Fin 2) = eqToHom (S.first.trans T.first.symm)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzagDiscrete.value S ≫ (eqToHom S.last.symm ≫ h.app (1 : Fin 2) ≫ eqToHom T.last) = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzagDiscrete.value T := by
  have hc : S.arrow (0 : Fin 1) ≫ h.app (1 : Fin 2) =
      h.app (0 : Fin 2) ≫ T.arrow (0 : Fin 1) := h.comm (0 : Fin 1)
  rw [hf] at hc
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzagDiscrete.value, Category.assoc, eqToHom_trans_assoc, eqToHom_trans,
    eqToHom_refl, Category.id_comp] using
      congrArg (fun z => eqToHom S.first.symm ≫ z ≫ eqToHom T.last) hc
lemma BackwardZigzag.value_moving {S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward) X Y}
    {T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward) X Y'} (h : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom S T)
    (hf : h.app (0 : Fin 2) = eqToHom (S.first.trans T.first.symm)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzagDiscrete.value S).val = (eqToHom S.last.symm ≫ h.app (1 : Fin 2) ≫ eqToHom T.last) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzagDiscrete.value T).val := by
  have hc : S.arrow (0 : Fin 1) ≫ h.app (0 : Fin 2) =
      h.app (1 : Fin 2) ≫ T.arrow (0 : Fin 1) := h.comm (0 : Fin 1)
  rw [hf] at hc
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzagDiscrete.value, Category.assoc, eqToHom_trans_assoc, eqToHom_trans,
    eqToHom_refl, Category.id_comp] using
      congrArg (fun z => eqToHom S.last.symm ≫ z ≫ eqToHom T.first) hc
end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
