module

public import SerrePositivity.EInfinity.Hammock.LocalizationValue
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ZigzagValueComparison
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.StrictLocalization

/-!
# 元の通常の局所化評価の相対自然性

概要：同じ元の相対関手に沿う通常の局所化 Hom の値を、固定端点の移送まで照合する。
方針：元の strictLocalizationMap_fac を評価の可換正方形へ代入する。
規約：元の Q.map、元の相対関手、元の局所化の対象表示を保持する。
使われ方：元の自由解像の全作用素に自然な右比較。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory SimplicialLocalization

variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  {W : MorphismProperty C} [W.IsMultiplicative] {V : MorphismProperty D} [V.IsMultiplicative]
  (F : LocalizerMorphism W V) {w : Word} {X Y : C} {X' Y' : D}

omit [W.IsMultiplicative] [V.IsMultiplicative] in
lemma localization_value_relative (S : Zigzag W w X Y) :
    HEq (Zigzag.Value.value V.Q V.Q_inverts (Zigzag.Relative.obj F S))
      ((strictLocalizationMap F).map (Zigzag.Value.value W.Q W.Q_inverts S)) :=
  Zigzag.Value.value_comparison F W.Q W.Q_inverts V.Q V.Q_inverts
    (strictLocalizationMap F) (strictLocalizationMap_fac F) S

omit [W.IsMultiplicative] [V.IsMultiplicative] in
lemma fixedLocalizationObject_eq (hX : F.functor.obj X = X') :
    (strictLocalizationMap F).obj (W.Q.obj X) = V.Q.obj X' :=
  (CategoryTheory.Functor.congr_obj (strictLocalizationMap_fac F) X).trans (congrArg V.Q.obj hX)

lemma localization_value_fixed (hX : F.functor.obj X = X') (hY : F.functor.obj Y = Y')
    (S : Zigzag W w X Y) :
    Zigzag.Value.value V.Q V.Q_inverts ((Zigzag.Relative.fixedFunctor F hX hY).obj S) =
      eqToHom (fixedLocalizationObject_eq F hX).symm ≫
        (strictLocalizationMap F).map (Zigzag.Value.value W.Q W.Q_inverts S) ≫
          eqToHom (fixedLocalizationObject_eq F hY) := by
  have h := Zigzag.Value.value_fixed_comparison F W.Q W.Q_inverts V.Q V.Q_inverts
    (strictLocalizationMap F) (strictLocalizationMap_fac F) hX hY S
  exact (conj_eqToHom_iff_heq _ _ (fixedLocalizationObject_eq F hX).symm
    (fixedLocalizationObject_eq F hY).symm).2 h

end SerrePositivity.EInfinity.Hammock
