module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagWordValuePath

/-!
# 元の全語の作用による zigzag の値の不変性

概要：元の任意の列の合成・恒等列の挿入は、元の zigzag の評価を保つ。
方針：値の射列を切断関手で制限した等式から元の全射の異種等式を回収する。
規約：元の端点の等式移送も含めた値の等式を結論とする。
使われ方：全語の余極限から局所化 Hom への評価の構成。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v u' v'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {W : MorphismProperty C} [W.IsMultiplicative] (L : C ⥤ D) (hL : W.IsInvertedBy L)
  {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : C}

lemma wordAction_value (f : a ⟶ b) (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.value L hL (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f S) = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.value L hL S := by
  have hh : HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.path L hL (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj f S)).hom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.path L hL S).hom := by
    have h := CategoryTheory.Functor.hcongr_hom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.path_wordAction L hL f S)
      (homOfLE (show (0 : Fin (b.length + 1)) ≤ Fin.last _ from Fin.zero_le _))
    refine h.trans ?_
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fin_map_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.path L hL S) f.cut_zero f.cut_last _ _
  apply eq_of_heq
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.value]
  simp only [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff,
    heq_eqToHom_comp_iff, heq_comp_eqToHom_iff]
  exact hh

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Value.wordAction_value export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization (wordAction_value)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
