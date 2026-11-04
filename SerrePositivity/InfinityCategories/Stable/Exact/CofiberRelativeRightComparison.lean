module

public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Opposite
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.NatTrans
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Logic.Equiv.Defs
public import SerrePositivity.InfinityCategories.Core.FunctorEvaluation
public import SerrePositivity.InfinityCategories.Core.Pullback
public import SerrePositivity.InfinityCategories.Core.PushoutShape
public import SerrePositivity.InfinityCategories.F1.SuspensionDiagramArrows
public import SerrePositivity.InfinityCategories.Stable.Exact.CofiberDiagrams

/-!
分割で生成：docstring を書き直すこと
概要：同じ底辺の全 cofiber 図式比較は、指定右辺の自然性とその始点の恒等性を保つ。
方針：全図式比較を右辺へ制限し、底辺の恒等式を共通頂点へ評価する。
規約：関手圏全体の二胞体を扱う。使われ方：商の右辺と C 単位の同時比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.CofiberDiagrams
variable (X : SSet.{u}) [Quasicategory X] [IsStable X]
  {A : SSet.{u}} [Quasicategory A] (f g : A ⟶ space X)
  (h : f ≫ bottom X = g ≫ bottom X)

omit [Quasicategory X] [IsStable X] [Quasicategory A] in
lemma bottomTarget_eq_rightSource :
    bottom X ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      right X ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
  rw [bottom, right]
  simp only [Category.assoc, stable_pre_evaluateFunctorAt]
  rfl

end SerrePositivity.KST.LocalizingInvariants.CofiberDiagrams
