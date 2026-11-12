module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FunctorSpace

/-!
概要：内部 Hom の宇宙移送と同じ元の射の後合成は全係数で可換。
方針：各単体の入力と出力の持ち上げを計算し、同型の往復で逆方向も回収する。
規約：同じ全族の射を保持。使われ方：模型比較の単位後合成と縮小の消去。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 元の後合成作用は、内部 Hom の同じ宇宙同型の順方向と可換。 -/
lemma uliftFunctorSpaceIso_post {X Y Z : SSet.{u}} (w : Y ⟶ Z) :
    (uliftFunctorSpaceIso.{u, v} X Y).hom ≫
      (ihom ((SSet.uliftFunctor.{v, u}).obj X)).map ((SSet.uliftFunctor.{v, u}).map w) =
    (SSet.uliftFunctor.{v, u}).map ((ihom X).map w) ≫
      (uliftFunctorSpaceIso.{u, v} X Z).hom := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro a
  apply CategoryTheory.Functor.functorHom_ext
  intro d α
  rfl

/-- 同じ後合成作用の宇宙移送を二つの元の同型で挟むと、元の持ち上げ作用に戻る。 -/
lemma uliftFunctorSpaceIso_inv_post_hom {X Y Z : SSet.{u}} (w : Y ⟶ Z) :
    (uliftFunctorSpaceIso.{u, v} X Y).inv ≫
      (SSet.uliftFunctor.{v, u}).map ((ihom X).map w) ≫
        (uliftFunctorSpaceIso.{u, v} X Z).hom =
    (ihom ((SSet.uliftFunctor.{v, u}).obj X)).map ((SSet.uliftFunctor.{v, u}).map w) := by
  rw [← uliftFunctorSpaceIso_post, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

end SerrePositivity.InfinityCategories.F2
