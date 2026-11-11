module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorHomTypedWhiskerAlgebra
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorHomIsIsoTransport
/-!
概要：同じ全関手射の正方形を、厳密な上げ下げを保つ持ち上げへ移送する。
方針：全前後合成の交換則と指定した同じ逆写像の恒等関係を使う。
規約：比較の値と全端点を保持。使われ方：元の実入力分解の自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet MonoidalClosed
lemma functorHomPrecomp_heq_of_source_eq {X Y Z : SSet.{u}} {f g : X ⟶ Y}
    (a : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f g) {p q : Z ⟶ X} (hp : p = q) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp f g p a) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPrecomp f g q a) := by
  subst q
  rfl
lemma functorHomPostcomp_heq_of_target_eq {X Y Z : SSet.{u}} {f g : X ⟶ Y}
    (a : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f g) {p q : Y ⟶ Z} (hp : p = q) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp f g p a) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorHomPostcomp f g q a) := by
  subst q
  rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories
