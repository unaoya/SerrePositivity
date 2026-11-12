module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SimplexPrismFirstVertex

/-!
概要：零面の最初の頂点は元の単体の第二頂点。
方針：全次数で標準単体と係数の二成分を計算する。
規約：係数に任意の単体集合を許す。
使われ方：比較三単体の零面の始点条件。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 零面の最初の頂点の全係数包含は元の第二頂点への全係数包含。 -/
lemma simplexPrismVertex_first_face_zero (n : ℕ) (A : SSet.{u}) :
    simplexPrismVertex n 0 A ≫ (stdSimplex.δ (0 : Fin (n + 2)) ▷ A) =
      simplexPrismVertex (n + 1) 1 A := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro a
  apply Prod.ext
  · apply stdSimplex.ext
    intro i
    apply Fin.ext
    rfl
  · rfl

end SerrePositivity.InfinityCategories.F2
