module

public import Mathlib.AlgebraicTopology.Quasicategory.Basic
public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Opposite
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
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
public import SerrePositivity.InfinityCategories.Core.TerminalVertices
public import SerrePositivity.InfinityCategories.Core.TrivialFibrationEquivalence
public import SerrePositivity.InfinityCategories.Core.ZeroTargetArrows
public import SerrePositivity.InfinityCategories.Stable.Definition
public import SerrePositivity.InfinityCategories.Stable.Exact.CofiberSquareFamily

/-!
分割で生成：docstring を書き直すこと
概要：安定な入力圏の suspension を全単体上の完全関手として選ぶ。
方針：零終点矢印の始点評価の切断と、普遍 cofiber 関手を合成する。
規約：値域 Sp の安定性は使わない。使われ方：差の C 側の shift の明示。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.SuspensionExact
variable (X : SSet.{u}) [Quasicategory X] [IsStable X]

def arrowSection : X ⟶ zeroTargetArrows X :=
  Classical.choose (trivialKanFibration_exists_section (zeroTargetArrowSource X))

lemma arrowSection_source : arrowSection X ≫ zeroTargetArrowSource X = 𝟙 X :=
  Classical.choose_spec (trivialKanFibration_exists_section (zeroTargetArrowSource X))

def arrow : X ⟶ (ihom (Δ[1] : SSet.{u})).obj X :=
  arrowSection X ≫ (fullSubcomplexOnVertices _ IsZeroTargetArrow).ι

lemma arrow_source : arrow X ≫
    evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = 𝟙 X :=
  arrowSection_source X

lemma arrow_zero_target (x : X _⦋0⦌) :
    IsZeroTargetArrow ((arrow X).app (Opposite.op ⦋0⦌) x) :=
  fullSubcomplexOnVertices_vertex ((arrowSection X).app (Opposite.op ⦋0⦌) x)

def map : X ⟶ X := arrow X ≫ CofiberFamily.cofiber X (𝟙 _)

end SerrePositivity.KST.LocalizingInvariants.SuspensionExact
