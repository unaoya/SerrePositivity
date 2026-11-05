module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.Basic.FunLike.Basic
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
public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.FunctorEvaluation
public import SerrePositivity.InfinityCategories.F1.Categories.CatInfinity
public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationBaseChange
public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationInfinity
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FunctorFamilyTranspose
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftStraighteningAllBases
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftStraighteningBaseChange
public import SerrePositivity.InfinityCategories.F1.Transport.SimplexSectionBaseChange
public import SerrePositivity.InfinityCategories.F1.Transport.FunctorIsoDoubleEvaluation

/-!
分割で生成：docstring を書き直すこと
 # 実分類写像の底変換は、同じ共同底変換の転置成分を保持する
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
variable {B D : SSet.{u}} (k : D ⟶ B)

/-- 二重評価は底の前合成の同じ頂点を厳密に回収する。 -/
theorem doubleFunctorEvaluation_precomp_vertex {K L A Y : SSet.{u}}
    (F : K ⟶ (ihom A).obj Y) (q : L ⟶ K) (l : L _⦋0⦌) (a : A _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.F1.Transport.doubleFunctorEvaluation (Y := Y) (q.app (Opposite.op ⦋0⦌) l) a).app
        (Opposite.op ⦋0⦌) (functorVertex F) =
      (_root_.SerrePositivity.InfinityCategories.F1.Transport.doubleFunctorEvaluation (Y := Y) l a).app (Opposite.op ⦋0⦌)
        (functorVertex (q ≫ F)) := by
  rw [_root_.SerrePositivity.InfinityCategories.F1.Transport.doubleFunctorEvaluation_vertex, _root_.SerrePositivity.InfinityCategories.F1.Transport.doubleFunctorEvaluation_vertex]
  rfl

/-- 実分類写像の元の底変換同型は、同じ共同同型の転置の端点だけを変更する。 -/
theorem leftStraighteningInfinityMap_baseChangeIso_heq :
    HEq (leftStraighteningInfinityMap_baseChangeIso k)
      (leftStraighteningSectionJointDiagram_baseChangeIso k).transpose := by
  unfold leftStraighteningInfinityMap_baseChangeIso
  dsimp only [_root_.id]
  have hcast {α β : Sort (u + 2)} (h : α = β) (x : α) : HEq (Eq.mp h x) x := by
    cases h
    rfl
  exact (hcast _ _).trans (hcast _ _)

end SerrePositivity.InfinityCategories.Stable.Straightening

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.doubleFunctorEvaluation_precomp_vertex := _root_.SerrePositivity.InfinityCategories.Stable.Straightening.doubleFunctorEvaluation_precomp_vertex

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.leftStraighteningInfinityMap_baseChangeIso_heq := _root_.SerrePositivity.InfinityCategories.Stable.Straightening.leftStraighteningInfinityMap_baseChangeIso_heq
