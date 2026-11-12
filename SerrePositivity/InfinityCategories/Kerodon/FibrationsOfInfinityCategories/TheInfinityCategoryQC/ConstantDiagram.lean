module
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic


/-!
概要：任意の形状 K に対する定値図式の対角関手。
方針：第二射影 K × C → C を curry する。
規約：各頂点だけでなく全ての高次単体を同時に定義する。
使われ方：filtered 性の対角関手の cofinality による判定。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

/-- 概要：対象を K 上の定値図式へ送る関手。
方針：直積の第二射影の内部 Hom 随伴を取る。
規約：K と C の充填性は不要。使われ方：対角関手の comma。 -/
def constantDiagram (K C : SSet.{u}) : C ⟶ (ihom K).obj C := curry (snd K C)

/-- 概要：定値図式の任意の族の評価は K の変数を忘れる。
方針：curry の自然性と往復則を使う。
規約：A の変数は保つ。使われ方：自然変換の族の終端条件。 -/
lemma uncurry_comp_constantDiagram {A K C : SSet.{u}} (f : A ⟶ C) :
    uncurry (f ≫ constantDiagram K C) = snd K A ≫ f := by
  rw [uncurry_natural_left, constantDiagram, uncurry_curry]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
