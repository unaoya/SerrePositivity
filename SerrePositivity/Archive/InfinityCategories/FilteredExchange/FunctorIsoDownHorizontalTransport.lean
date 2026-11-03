module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorIsoDownHorizontal

/-!
概要：大きい二つの指定比較を明示した元の射の表示へ揃え、水平合成を下降する。
方針：明示した二つの始域射の等式を消去し、水平合成の下降の式を使う。
規約：指定二比較と四端点を保持。使われ方：元の native 合成比較の四射表示。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 明示した二射の表示の下で、元の大きい二比較の水平合成も同じ指定値へ下降する。 -/
lemma functorIsoDown_horizontal_ofEq {A B C : SSet.{u}} [Quasicategory B] [Quasicategory C]
    {f f' : A ⟶ B} {g g' : B ⟶ C}
    {a : (SSet.uliftFunctor.{v, u}).obj A ⟶ (SSet.uliftFunctor.{v, u}).obj B}
    {b : (SSet.uliftFunctor.{v, u}).obj B ⟶ (SSet.uliftFunctor.{v, u}).obj C}
    (e : FunctorIso a ((SSet.uliftFunctor.{v, u}).map f'))
    (d : FunctorIso b ((SSet.uliftFunctor.{v, u}).map g'))
    (ha : a = (SSet.uliftFunctor.{v, u}).map f)
    (hb : b = (SSet.uliftFunctor.{v, u}).map g) :
    functorIsoDown (functorIsoOfEq
      (e.postcomp b ≪≫ d.precomp ((SSet.uliftFunctor.{v, u}).map f'))
      (by rw [ha, hb, ← Functor.map_comp])
      ((SSet.uliftFunctor.{v, u}).map_comp f' g').symm) =
    (functorIsoDown (functorIsoOfEq e ha rfl)).postcomp g ≪≫
      (functorIsoDown (functorIsoOfEq d hb rfl)).precomp f' := by
  subst a b
  exact functorIsoDown_horizontal e d

end SerrePositivity.InfinityCategories.F2
