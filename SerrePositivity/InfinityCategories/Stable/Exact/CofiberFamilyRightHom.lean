module

public import Mathlib.AlgebraicTopology.Quasicategory.Basic
public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
public import Mathlib.AlgebraicTopology.SimplicialSet.HomotopyCat
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.AlgebraicTopology.SimplicialSet.RelativeMorphism
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Opposite
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.NatTrans
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Subfunctor.Basic
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.FunctorEvaluation
public import SerrePositivity.InfinityCategories.Core.KanHomotopyEquivalence
public import SerrePositivity.InfinityCategories.Core.Pullback
public import SerrePositivity.InfinityCategories.Core.PushoutShape
public import SerrePositivity.InfinityCategories.F1.SuspensionDiagramArrows
public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.FunctorHomCorrespondence
public import SerrePositivity.InfinityCategories.Stable.Definition
public import SerrePositivity.InfinityCategories.Stable.Quasicategory.ArrowFamilyHomotopy
public import SerrePositivity.InfinityCategories.Stable.Exact.CofiberSquareFamily

/-!
分割で生成：docstring を書き直すこと
概要：元の cofiber 全族の右辺を自然変換として保持する。
方針：右辺の prism を取り出し、零始点の場合の可逆性を各成分から示す。
規約：cofiber の比較を選び直さない。使われ方：C 随伴単位との同時比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.CofiberFamily
variable (X : SSet.{u}) [Quasicategory X] [IsStable X]
  {A : SSet.{u}} (a : A ⟶ (ihom (Δ[1] : SSet.{u})).obj X)

def rightArrow : A ⟶ (ihom (Δ[1] : SSet.{u})).obj X :=
  squares X a ≫ (pre squareRightEdge).app X

lemma rightArrow_source : rightArrow X a ≫
    evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      a ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
  conv_rhs => rw [← squares_bottom X a]
  rw [rightArrow]
  simp only [Category.assoc, stable_pre_evaluateFunctorAt]
  rfl

lemma rightArrow_target : rightArrow X a ≫
    evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = cofiber X a := by
  rw [rightArrow, Category.assoc, stable_pre_evaluateFunctorAt]
  rfl

def rightHomotopy : SSet.Homotopy
    (a ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) (cofiber X a) where
  h := (arrowFamilyHomotopy (rightArrow X a)).h
  h₀ := by
    rw [(arrowFamilyHomotopy (rightArrow X a)).h₀]
    exact congrArg (fun f => (SSet.RelativeMorphism.botEquiv.symm f).map)
      (rightArrow_source X a)
  h₁ := by
    rw [(arrowFamilyHomotopy (rightArrow X a)).h₁]
    exact congrArg (fun f => (SSet.RelativeMorphism.botEquiv.symm f).map)
      (rightArrow_target X a)
  rel := (arrowFamilyHomotopy (rightArrow X a)).rel

def rightHom : FunctorHom
    (a ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) (cofiber X a) :=
  Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy (rightHomotopy X a))

end SerrePositivity.KST.LocalizingInvariants.CofiberFamily
