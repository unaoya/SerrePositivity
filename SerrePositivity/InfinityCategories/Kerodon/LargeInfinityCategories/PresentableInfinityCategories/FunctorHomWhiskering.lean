module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomCorrespondence

/-!
概要：h Fun の射の前合成と後合成の可換性。
方針：元の関手単体集合の作用を同じホモトピー圏へ移す。
規約：対象の再選択や点ごとの射への弱化をしない。
使われ方：密度から構成した反映の三角恒等式。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：ホモトピー圏への写像は合成の射作用を保つ。
方針：元の関手の合成保存を使う。
規約：同じ両端と射を保つ。
使われ方：前後合成の正規化。 -/
lemma hoFunctor_map_comp_apply {A B D : SSet.{u}} (f : A ⟶ B) (g : B ⟶ D)
    {x y : hoFunctor.obj A} (η : x ⟶ y) :
    (hoFunctor.map (f ≫ g)).toFunctor.map η =
      (hoFunctor.map g).toFunctor.map ((hoFunctor.map f).toFunctor.map η) := by
  have h := CategoryTheory.Functor.congr_hom
    (congrArg Cat.Hom.toFunctor (hoFunctor.map_comp f g)) η
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id, Cat.Hom.comp_map] using h

/-- 概要：h Fun の射の前後合成は可換。
方針：二通りの全パラメータの作用を同定する。
規約：同じ射の像を比較する。
使われ方：単位の制限の後合成。 -/
lemma functorHom_pre_post {A B X Y : SSet.{u}} (i : A ⟶ B) (q : X ⟶ Y)
    {F G : B ⟶ X} (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F G) :
    (hoFunctor.map ((pre i).app Y)).toFunctor.map
      ((hoFunctor.map ((ihom B).map q)).toFunctor.map η) =
    (hoFunctor.map ((ihom A).map q)).toFunctor.map
      ((hoFunctor.map ((pre i).app X)).toFunctor.map η) := by
  rw [← hoFunctor_map_comp_apply, ← hoFunctor_map_comp_apply]
  rfl

/-- 概要：合成した前合成は h Fun の射でも順次の前合成に一致する。
方針：同じ制限関手の合成を使う。
規約：合成の向きを保持する。
使われ方：Yoneda と包含による二重制限。 -/
lemma functorHom_pre_comp {A B D X : SSet.{u}} (i : A ⟶ B) (j : B ⟶ D)
    {F G : D ⟶ X} (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F G) :
    (hoFunctor.map ((pre (i ≫ j)).app X)).toFunctor.map η =
    (hoFunctor.map ((pre i).app X)).toFunctor.map
      ((hoFunctor.map ((pre j).app X)).toFunctor.map η) := by
  rw [← hoFunctor_map_comp_apply]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
