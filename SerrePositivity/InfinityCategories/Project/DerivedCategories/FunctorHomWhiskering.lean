module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorHomWhiskerExchange
/-!
概要：指定された全関手射の制限と比較を、元の値を保って照合する。
方針：同じ端点・全関手圏の作用・実包含後の一致を使う。
規約：射の可逆性と追加の平坦性は不要。使われ方：ξ と κ の全射自然性。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet MonoidalClosed
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
def functorHomPostcomp {X Y Z : SSet.{u}}
    (f g : X ⟶ Y) (q : Y ⟶ Z) (e : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f g) : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (f ≫ q) (g ≫ q) :=
  (SSet.mapHomotopyCategory ((ihom X).map q)).map e
def functorHomPrecomp {W X Y : SSet.{u}}
    (f g : X ⟶ Y) (p : W ⟶ X) (e : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f g) : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (p ≫ f) (p ≫ g) :=
  (SSet.mapHomotopyCategory ((pre p).app Y)).map e
end
end SerrePositivity.InfinityCategories.Project.DerivedCategories
