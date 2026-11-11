module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoPair

/-!
概要：第二成分を固定した関手空間の組と、二つの実射の直積作用は厳密に可換する。
方針：元の curry と評価を次数ごとに計算する。
規約：二つの実射と係数を保持。使われ方：全右 Hom 比較の輸送作用の因子の同定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 元の組の後の二成分の直積作用は、元の第一成分への作用後の同じ組と一致する。 -/
lemma functorPairRight_tensor {P A B C D : SSet.{u}} (y : P ⟶ B) (f : A ⟶ C) (g : B ⟶ D) :
    functorPairRight y ≫ (ihom P).map (f ⊗ₘ g) =
      (ihom P).map f ≫ functorPairRight (y ≫ g) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro a
  apply CategoryTheory.Functor.functorHom_ext
  intro d α
  apply ConcreteCategory.hom_ext
  intro p
  rfl

end SerrePositivity.InfinityCategories.F2
