module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedRightFamilyCoefficient

/-!
概要：同じ全係数で動く点と二射の評価は、豊穣合成の評価に厳密に一致する。
方針：元の内部 Hom の評価を、全次数の同じ単体で計算する。
規約：点も二射も固定しない。
使われ方：指定した二段の値比較と合成射の値比較の端点の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
/-- 概要：同じ動く二射による二段評価と合成評価の厳密な一致。
方針：豊穣合成と評価の単体を直接計算する。規約：全係数を保持。使われ方：合成比較。 -/
lemma pointedRightFamilyEvaluation_comp {K M L : KanObject.{u}} {P : SSet.{u + 1}}
    (x : P ⟶ (SSet.uliftFunctor.{u + 1, u}).obj K.obj)
    (y : P ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom K M))
    (z : P ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom M L)) :
    pointedRightFamilyEvaluation (pointedRightFamilyEvaluation x y) z =
      pointedRightFamilyEvaluation x (lift y z ≫ coherentHomComposition K M L) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro p
  apply ULift.ext
  rfl
end SerrePositivity.InfinityCategories.F2
