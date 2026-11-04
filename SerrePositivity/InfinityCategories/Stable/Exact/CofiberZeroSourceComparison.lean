module

public import Mathlib.AlgebraicTopology.Quasicategory.Basic
public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.PushoutProduct
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.Basic.Opposite
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Types.Basic
public import SerrePositivity.InfinityCategories.Core.FullSubcomplexFibration
public import SerrePositivity.InfinityCategories.Stable.ZeroSourceArrows

/-!
分割で生成：docstring を書き直すこと
概要：零始点を持つ任意の矢印族の cofiber は、その終点の族と関手として同型。
方針：零始点矢印の終点評価の同値で右随伴の像と比較し、可逆余単位を使う。
規約：対象ごとの同型に弱めない。使われ方：差の関手と D 包含の合成の計算。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
variable (X : SSet.{u}) [Quasicategory X] [IsStable X]
  {A : SSet.{u}} (a : A ⟶ (ihom (Δ[1] : SSet.{u})).obj X)
  (ha : ∀ x, IsZeroSourceArrow (a.app (Opposite.op ⦋0⦌) x))

local instance cofiberZeroComparisonQuasicategory : Quasicategory (zeroSourceArrows X) :=
  fullSubcomplexOnVertices_quasicategory _ _

end SerrePositivity.KST.LocalizingInvariants
