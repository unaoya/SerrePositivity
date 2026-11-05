module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Opposite
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Iso
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
public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.InternalHomFlipAdjunction
public import SerrePositivity.InfinityCategories.Core.InternalHomSwap
public import SerrePositivity.InfinityCategories.F1.Categories.CatInfinity
public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationInfinity
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FunctorFamilyTranspose
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftStraighteningAllBases
public import SerrePositivity.InfinityCategories.F1.Transport.SimplexDomains
public import SerrePositivity.InfinityCategories.F1.Transport.SimplexFirstVertex
public import SerrePositivity.InfinityCategories.F1.Transport.SimplexSectionBaseChange
public import SerrePositivity.InfinityCategories.F1.Transport.SimplexSectionDiagram

/-!
分割で生成：docstring を書き直すこと
 # 初頂点制限の同じ切断比較を、元の切断空間の指定成分として固定する
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
namespace SerrePositivity.InfinityCategories.Stable.Straightening
open SerrePositivity.KST.Fibration
variable {B : SSet.{u}}

/-- 分類写像側の元の制限同型は、同じ共同制限同型の転置の端点だけを変更する。 -/
theorem leftStraighteningInfinityMap_restrictIso_heq_transpose :
    HEq (leftStraighteningInfinityMap_restrictIso B)
      (leftStraighteningSectionJointDiagram_restrictIso B).transpose := by
  unfold leftStraighteningInfinityMap_restrictIso
  dsimp only [_root_.id]
  have hcast {α β : Sort (u + 2)} (h : α = β) (x : α) : HEq (Eq.mp h x) x := by
    cases h
    rfl
  exact hcast _ _

end SerrePositivity.InfinityCategories.Stable.Straightening

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.leftStraighteningInfinityMap_restrictIso_heq_transpose := _root_.SerrePositivity.InfinityCategories.Stable.Straightening.leftStraighteningInfinityMap_restrictIso_heq_transpose
