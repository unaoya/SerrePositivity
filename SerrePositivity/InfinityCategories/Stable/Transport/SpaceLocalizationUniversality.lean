module
public import Mathlib.AlgebraicTopology.Quasicategory.Basic
public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.PushoutProduct
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.CompStructTruncated
public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Opposite
public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.NatTrans
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Data.Set.Defs
public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.InvertibleEdgeLifting
public import SerrePositivity.InfinityCategories.F1.Categories.CatInfinity
public import SerrePositivity.InfinityCategories.F1.Universe.InvertibleEdge
public import SerrePositivity.InfinityCategories.F1B.Localization.Localization

/-!
分割で生成：docstring を書き直すこと
 # 元の小さい商局所化の、宇宙を揃えた空間値関手 ∞ 圏での普遍性
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration

/-- 同じ指定辺の反転は、実際の可逆辺とその逆データの宇宙持ち上げで保たれる。 -/
theorem invertsEdges_ulift {X Q : SSet.{u}} [Quasicategory Q] (q : X ⟶ Q)
    (W : Set (X _⦋1⦌)) (hq : InvertsEdges q W) :
    InvertsEdges ((SSet.uliftFunctor.{u + 1, u}).map q) (ULift.up '' W) := by
  rintro s ⟨t, ht, rfl⟩
  have hi := IsInvertibleEdge.ulift.{u, u + 1} (hq ht)
  exact (isInvertibleEdge_congr (show
    (uliftTruncatedEdge ((edgeOfSimplex t).map ((truncation 2).map q))).edge =
      ((edgeOfSimplex (ULift.up t)).map
        ((truncation 2).map ((SSet.uliftFunctor.{u + 1, u}).map q))).edge from rfl)).mp hi

variable {X Q : SSet.{u}} [Quasicategory Q] (q : X ⟶ Q)
  (W : Set (X _⦋1⦌)) (hq : IsLocalization q W)

/-- 元の商への前合成を、空間値の全反転関手の実際の全部分複体に値を取る射として保持する。 -/
def spaceLocalizationPrecomposition :
    (ihom ((SSet.uliftFunctor.{u + 1, u}).obj Q)).obj SpaceInfinity.{u} ⟶
      invertingFunctors ((SSet.uliftFunctor.{u + 1, u}).obj X) SpaceInfinity.{u} (ULift.up '' W) :=
  localizationPrecomposition ((SSet.uliftFunctor.{u + 1, u}).map q) (ULift.up '' W)
    (invertsEdges_ulift q W hq.choose) SpaceInfinity

end SerrePositivity.KST.Fibration
