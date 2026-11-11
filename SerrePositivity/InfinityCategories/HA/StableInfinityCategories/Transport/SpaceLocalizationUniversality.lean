module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
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
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.InvertibleEdge
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Localization

/-!
分割で生成：docstring を書き直すこと
 # 元の小さい商局所化の、宇宙を揃えた空間値関手 ∞ 圏での普遍性
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport
open _root_.SerrePositivity.KST.Fibration

/-- 同じ指定辺の反転は、実際の可逆辺とその逆データの宇宙持ち上げで保たれる。 -/
theorem invertsEdges_ulift {X Q : SSet.{u}} [Quasicategory Q] (q : X ⟶ Q)
    (W : Set (X _⦋1⦌)) (hq : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges q W) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges ((SSet.uliftFunctor.{u + 1, u}).map q) (ULift.up '' W) := by
  rintro s ⟨t, ht, rfl⟩
  have hi := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.IsInvertibleEdge.ulift.{u, u + 1} (hq ht)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (show
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftTruncatedEdge ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex t).map ((truncation 2).map q))).edge =
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (ULift.up t)).map
        ((truncation 2).map ((SSet.uliftFunctor.{u + 1, u}).map q))).edge from rfl)).mp hi

variable {X Q : SSet.{u}} [Quasicategory Q] (q : X ⟶ Q)
  (W : Set (X _⦋1⦌)) (hq : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IsLocalization q W)

/-- 元の商への前合成を、空間値の全反転関手の実際の全部分複体に値を取る射として保持する。 -/
def spaceLocalizationPrecomposition :
    (ihom ((SSet.uliftFunctor.{u + 1, u}).obj Q)).obj _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertingFunctors ((SSet.uliftFunctor.{u + 1, u}).obj X) _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} (ULift.up '' W) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.localizationPrecomposition ((SSet.uliftFunctor.{u + 1, u}).map q) (ULift.up '' W)
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.invertsEdges_ulift q W hq.choose) _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.invertsEdges_ulift := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.invertsEdges_ulift

@[deprecated _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.spaceLocalizationPrecomposition (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.spaceLocalizationPrecomposition := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.spaceLocalizationPrecomposition

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.spaceLocalizationPrecomposition._proof_1 := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.spaceLocalizationPrecomposition._proof_1
