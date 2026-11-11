module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CellOverNaturality
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SimplexCellIndex
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold.ScaffoldFiniteNerveUniverse
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan

/-!
概要：任意次元の最初の辺と尾部を、元の通常圏のセルの cospan に束ねる。
方針：共有頂点を一つ固定し、二つの包含関手の合成を同じ通常関手として照合する。
規約：元の全局所 Hom と分類の同じ制限を使う。
使われ方：元の分類 Hom 作用の高次単体への帰納。

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

variable (n : ℕ) {C : Type u} [Category.{u} C] (k : ULift.{u} (Fin (n + 2)) ⥤ C)

/-- 元の有限鎖の最初の辺セル。 -/
def cocartesianScaffoldFirstCell : ULift.{u} (Fin 2) ⥤ C := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteFirstEdge n ⋙ k

/-- 元の有限鎖の尾部セル。 -/
def cocartesianScaffoldTailCell : ULift.{u} (Fin (n + 1)) ⥤ C := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteTail n ⋙ k

/-- 最初の辺の終点として固定する共有セル。 -/
def cocartesianScaffoldSharedCell : ULift.{u} (Fin 1) ⥤ C :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSimplexCellIndex (SimplexCategory.δ (0 : Fin 2)) ⋙ cocartesianScaffoldFirstCell n k

/-- 尾部の零頂点も同じ共有セルを表す。 -/
lemma cocartesianScaffoldSharedCell_tail :
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold.scaffoldFiniteZeroVertex n ⋙ cocartesianScaffoldTailCell n k =
      cocartesianScaffoldSharedCell n k := by
  have h : _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold.scaffoldFiniteZeroVertex n ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteTail n =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSimplexCellIndex (SimplexCategory.δ (0 : Fin 2)) ⋙
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteFirstEdge.{u} n := by
    refine CategoryTheory.Functor.ext (fun i ↦ ?_) (fun _ _ _ ↦ Subsingleton.elim _ _)
    obtain ⟨i⟩ := i
    fin_cases i
    rfl
  exact congrArg (fun f ↦ f ⋙ k) h

/-- 同じ共有セルから最初の辺への元の底上の射。 -/
def cocartesianScaffoldSharedToFirst :
    Over.mk (nerveMap (cocartesianScaffoldSharedCell n k)) ⟶
      Over.mk (nerveMap (cocartesianScaffoldFirstCell n k)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianCellOverMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSimplexCellIndex (SimplexCategory.δ (0 : Fin 2)))
    (cocartesianScaffoldFirstCell n k) (cocartesianScaffoldSharedCell n k) rfl

/-- 同じ共有セルから尾部への元の底上の射。 -/
def cocartesianScaffoldSharedToTail :
    Over.mk (nerveMap (cocartesianScaffoldSharedCell n k)) ⟶
      Over.mk (nerveMap (cocartesianScaffoldTailCell n k)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianCellOverMap (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold.scaffoldFiniteZeroVertex n)
    (cocartesianScaffoldTailCell n k) (cocartesianScaffoldSharedCell n k)
    (cocartesianScaffoldSharedCell_tail n k)

/-- 元の二成分と一つの共有セルの、同じ底上の反変 cospan。 -/
def cocartesianScaffoldCellCospan : WalkingCospan ⥤ (Over (nerve C))ᵒᵖ :=
  cospan (cocartesianScaffoldSharedToFirst n k).op (cocartesianScaffoldSharedToTail n k).op

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
