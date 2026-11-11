module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CellOverNaturality
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SimplexCellIndex
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan

/-!
概要：二次元セルの二辺と同じ共有頂点を、実際の底上の cospan として指定する。
方針：元の面のセル添字と共有頂点の等式を同じ底上の射に束ねる。
規約：二つの頂点表示を別々の比較にしない。
使われ方：源・標的の同じ Segal 比較図式。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

variable {C : Type u} [Category.{u} C] (k : ULift.{u} (Fin 3) ⥤ C)

/-- 元の二次元セルの最初の辺。 -/
def cocartesianTwoSimplexFirstCell : ULift.{u} (Fin 2) ⥤ C :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSimplexCellIndex (SimplexCategory.δ (2 : Fin 3)) ⋙ k

/-- 元の二次元セルの次の辺。 -/
def cocartesianTwoSimplexSecondCell : ULift.{u} (Fin 2) ⥤ C :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSimplexCellIndex (SimplexCategory.δ (0 : Fin 3)) ⋙ k

/-- 同じ二辺で共有する、元の唯一の頂点セル。 -/
def cocartesianTwoSimplexSharedCell : ULift.{u} (Fin 1) ⥤ C :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSimplexCellIndex (SimplexCategory.δ (0 : Fin 2)) ⋙
    cocartesianTwoSimplexFirstCell k

/-- 次の辺の始点も、同じ共有セルそのもの。 -/
lemma cocartesianTwoSimplexSharedCell_second :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSimplexCellIndex (SimplexCategory.δ (1 : Fin 2)) ⋙
      cocartesianTwoSimplexSecondCell k = cocartesianTwoSimplexSharedCell k := by
  exact congrArg (fun f ↦ f ⋙ k) _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSimplexCellIndex_twoSimplex_sharedVertex.symm

/-- 同じ共有頂点から最初の辺への、元の底上の射。 -/
def cocartesianTwoSimplexSharedToFirst :
    Over.mk (nerveMap (cocartesianTwoSimplexSharedCell k)) ⟶
      Over.mk (nerveMap (cocartesianTwoSimplexFirstCell k)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianCellOverMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSimplexCellIndex (SimplexCategory.δ (0 : Fin 2)))
    (cocartesianTwoSimplexFirstCell k) (cocartesianTwoSimplexSharedCell k) rfl

/-- 同じ共有頂点から次の辺への、元の底上の射。 -/
def cocartesianTwoSimplexSharedToSecond :
    Over.mk (nerveMap (cocartesianTwoSimplexSharedCell k)) ⟶
      Over.mk (nerveMap (cocartesianTwoSimplexSecondCell k)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianCellOverMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSimplexCellIndex (SimplexCategory.δ (1 : Fin 2)))
    (cocartesianTwoSimplexSecondCell k) (cocartesianTwoSimplexSharedCell k)
    (cocartesianTwoSimplexSharedCell_second k)

/-- 同じ二辺と同じ共有頂点を表す、元の底上の反変 cospan。 -/
def cocartesianTwoSimplexCellCospan : WalkingCospan ⥤ (Over (nerve C))ᵒᵖ :=
  cospan (cocartesianTwoSimplexSharedToFirst k).op (cocartesianTwoSimplexSharedToSecond k).op

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
