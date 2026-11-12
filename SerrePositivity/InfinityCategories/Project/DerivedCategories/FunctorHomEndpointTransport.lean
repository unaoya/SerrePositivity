module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorHomWhiskering
/-!
概要：元の augmentation の自然性を、二射影と同じ指定入力切断の表示へ移す。
方針：同じ全関手射の端点輸送と二段前合成の整合性を保つ。
規約：指定比較と切断・計算上限を変更しない。使われ方：元の κ の自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
def functorHomOfMapEq {X Y : SSet.{w}} {f g f' g' : X ⟶ Y}
    (a : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f g) (hf : f = f') (hg : g = g') : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f' g' := by
  cases hf
  cases hg
  exact a
lemma functorHomOfMapEq_heq {X Y : SSet.{w}} {f g f' g' : X ⟶ Y}
    (a : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f g) (hf : f = f') (hg : g = g') :
    HEq (functorHomOfMapEq a hf hg) a := by
  cases hf
  cases hg
  rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories
