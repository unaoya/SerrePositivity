module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.HomotopyCat
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Opposite
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Logic.Equiv.Defs
public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.FunctorEvaluation
public import SerrePositivity.InfinityCategories.Core.KanHomotopyEquivalence
public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.FunctorHomCorrespondence
public import SerrePositivity.InfinityCategories.Stable.Quasicategory.ArrowFamilyHomotopy

/-!
分割で生成：docstring を書き直すこと
概要：矢印全族が表す自然変換は、パラメータ制限と図式比較に自然。
方針：元の prism の前合成を照合し、関手圏内の交換則を適用する。
規約：各点での可換性に弱めない。使われ方：cofiber の全図式比較の指定右辺。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.Stable.Quasicategory
open SerrePositivity.KST.LocalizingInvariants

def arrowFamilyHom {A X : SSet.{u}} (a : A ⟶ (ihom (Δ[1] : SSet.{u})).obj X) :
    FunctorHom (a ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
      (a ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) :=
  Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy (arrowFamilyHomotopy a))

end SerrePositivity.InfinityCategories.Stable.Quasicategory

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.arrowFamilyHom (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.arrowFamilyHom := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.arrowFamilyHom

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.arrowFamilyHom._proof_1 := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.arrowFamilyHom._proof_1
