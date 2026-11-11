module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ParametrizedSections

/-!
概要：パラメータ付き相対切断の前合成と、その厳密な関手則。
方針：元の底の族の等式を用いて、内部 Hom の前合成を同じ引き戻しへ持ち上げる。
規約：底のパラメータを動かさず、対象間の等式による置き換えも明示する。
使われ方：通常の under 圏の反変性を strict な fibration 図式にする。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

/-- 同じ底の族を保つ前合成による相対切断の制限。 -/
def parametrizedSectionsPre {A D E Y P : SSet.{u}} (p : E ⟶ Y)
    (a : P ⟶ (ihom A).obj Y) (b : P ⟶ (ihom D).obj Y) (i : D ⟶ A)
    (h : a ≫ (pre i).app Y = b) : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.parametrizedSections p a ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.parametrizedSections p b :=
  pullback.lift (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.parametrizedSectionsMap p a ≫ (pre i).app E)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.parametrizedSectionsProjection p a) (by
      rw [Category.assoc, ← (pre i).naturality p, ← Category.assoc,
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.parametrizedSections_condition, Category.assoc, h])

lemma parametrizedSectionsPre_map {A D E Y P : SSet.{u}} (p : E ⟶ Y)
    (a : P ⟶ (ihom A).obj Y) (b : P ⟶ (ihom D).obj Y) (i : D ⟶ A)
    (h : a ≫ (pre i).app Y = b) :
    parametrizedSectionsPre p a b i h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.parametrizedSectionsMap p b =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.parametrizedSectionsMap p a ≫ (pre i).app E := pullback.lift_fst _ _ _

lemma parametrizedSectionsPre_projection {A D E Y P : SSet.{u}} (p : E ⟶ Y)
    (a : P ⟶ (ihom A).obj Y) (b : P ⟶ (ihom D).obj Y) (i : D ⟶ A)
    (h : a ≫ (pre i).app Y = b) :
    parametrizedSectionsPre p a b i h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.parametrizedSectionsProjection p b =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.parametrizedSectionsProjection p a := pullback.lift_snd _ _ _

/-- 同じ制限は恒等射を厳密に保つ。 -/
lemma parametrizedSectionsPre_id {A E Y P : SSet.{u}} (p : E ⟶ Y)
    (a : P ⟶ (ihom A).obj Y) :
    parametrizedSectionsPre p a a (𝟙 A)
      (by rw [pre_id, NatTrans.id_app, Category.comp_id]) = 𝟙 _ := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.parametrizedSections_hom_ext p a
  · rw [parametrizedSectionsPre_map, pre_id, NatTrans.id_app,
      Category.comp_id, Category.id_comp]
  · rw [parametrizedSectionsPre_projection, Category.id_comp]

/-- 同じ制限は前合成の逆順の合成を厳密に保つ。 -/
lemma parametrizedSectionsPre_comp {A D T E Y P : SSet.{u}} (p : E ⟶ Y)
    (a : P ⟶ (ihom A).obj Y) (b : P ⟶ (ihom D).obj Y) (c : P ⟶ (ihom T).obj Y)
    (i : D ⟶ A) (j : T ⟶ D)
    (hi : a ≫ (pre i).app Y = b) (hj : b ≫ (pre j).app Y = c)
    (hij : a ≫ (pre (j ≫ i)).app Y = c) :
    parametrizedSectionsPre p a b i hi ≫ parametrizedSectionsPre p b c j hj =
      parametrizedSectionsPre p a c (j ≫ i) hij := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.parametrizedSections_hom_ext p c
  · rw [Category.assoc, parametrizedSectionsPre_map, ← Category.assoc,
      parametrizedSectionsPre_map, parametrizedSectionsPre_map]
    rw [Category.assoc, ← NatTrans.comp_app, ← pre_map]
  · rw [Category.assoc, parametrizedSectionsPre_projection,
      parametrizedSectionsPre_projection, parametrizedSectionsPre_projection]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
