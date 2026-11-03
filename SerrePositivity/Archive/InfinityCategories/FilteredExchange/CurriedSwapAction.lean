module

public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes

/-!
概要：二係数の作用を curry し、任意の動く第二係数に制限した実円柱を回収する。
方針：curry の自然性と直積の交換を計算する。
規約：元の全パラメータと全次数の射を保持する。
使われ方：指定精密化の Hom 作用円柱を同じ関手空間の path へ戻す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 二係数作用を curry して元の動く係数で制限すると同じ全係数円柱。 -/
lemma curriedSwapAction_uncurry {A H P Y : SSet.{u}} (r : P ⟶ H) (m : H ⊗ A ⟶ Y) :
    uncurry (r ≫ curry ((β_ A H).hom ≫ m)) =
      lift (snd A P ≫ r) (fst A P) ≫ m := by
  rw [uncurry_natural_left, uncurry_curry, ← Category.assoc]
  congr 1

end SerrePositivity.InfinityCategories.F2
