module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.CompStruct
public import Mathlib.AlgebraicTopology.SimplicialSet.CompStructTruncated
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
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
public import Mathlib.CategoryTheory.Iso
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
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
public import SerrePositivity.InfinityCategories.Core.FunctorHomotopy
public import SerrePositivity.InfinityCategories.Core.InternalHomFlipAdjunction
public import SerrePositivity.InfinityCategories.Core.InternalHomSwap
public import SerrePositivity.InfinityCategories.Stable.Quasicategory.CoconeFamilyCoreComparison

/-!
分割で生成：docstring を書き直すこと
概要：全余錐比較の同じ一次単体を、両変数の制限を保持する同じ全 prism へ移す。
方針：元の内部 Hom 交換と uncurry の自然性で全写像を計算する。
規約：端点の代表・比較辺・区間を選び直さず、元の一次単体だけを使う。
使われ方：K 始端比較と指定 S 始端比較の両制限一致を相対 Homotopy 延長へ渡す。
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

def spanComparisonPrism {K L X : SSet.{u}}
    (s : ((ihom L).obj ((ihom K).obj X)) _⦋1⦌) : K ⊗ (Δ[1] : SSet.{u}) ⟶ (ihom L).obj X :=
  uncurry (SSet.yonedaEquiv.symm s ≫ (internalHomSwapIso L K X).hom)

lemma spanComparisonPrism_pre_parameter {K K' L X : SSet.{u}} (j : K' ⟶ K)
    (s : ((ihom L).obj ((ihom K).obj X)) _⦋1⦌) :
    (j ▷ (Δ[1] : SSet.{u})) ≫ _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.spanComparisonPrism s =
      _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.spanComparisonPrism (((ihom L).map ((pre j).app X)).app (Opposite.op ⦋1⦌) s) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.spanComparisonPrism]
  rw [← uncurry_pre_app, Category.assoc,
    ← internalHomSwapIso_pre, ← SSet.yonedaEquiv_symm_comp]
  rfl

/-- 元の全比較辺そのものを戻して得る、元の全パラメータ族間の実 Homotopy。 -/
def spanFunctorEdgeUnflipHomotopy {K L X : SSet.{u}} {F G : K ⟶ (ihom L).obj X}
    (l : Truncated.Edge (X := (truncation 2).obj ((ihom L).obj ((ihom K).obj X)))
      (functorVertex (internalHomFlipHomEquiv K L X F))
      (functorVertex (internalHomFlipHomEquiv K L X G))) : SSet.Homotopy F G :=
  simplicialHomotopyOfFunctorEdge (_root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.spanFunctorEdgeUnflip l).toTruncated

lemma spanFunctorEdgeUnflipHomotopy_h {K L X : SSet.{u}} {F G : K ⟶ (ihom L).obj X}
    (l : Truncated.Edge (X := (truncation 2).obj ((ihom L).obj ((ihom K).obj X)))
      (functorVertex (internalHomFlipHomEquiv K L X F))
      (functorVertex (internalHomFlipHomEquiv K L X G))) :
    (_root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.spanFunctorEdgeUnflipHomotopy l).h = _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.spanComparisonPrism l.edge := by
  change uncurry (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.spanFunctorEdgeUnflip l).edge) =
    uncurry (SSet.yonedaEquiv.symm l.edge ≫ (internalHomSwapIso L K X).hom)
  rw [_root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.spanFunctorEdgeUnflip_edge, ← SSet.yonedaEquiv_symm_comp]
  rfl

end SerrePositivity.InfinityCategories.Stable.Quasicategory

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.spanComparisonPrism (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.spanComparisonPrism := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.spanComparisonPrism

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.spanComparisonPrism_pre_parameter := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.spanComparisonPrism_pre_parameter

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.spanFunctorEdgeUnflipHomotopy (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.spanFunctorEdgeUnflipHomotopy := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.spanFunctorEdgeUnflipHomotopy

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.spanFunctorEdgeUnflipHomotopy_h := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.spanFunctorEdgeUnflipHomotopy_h

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.spanComparisonPrism.eq_1 := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.spanComparisonPrism.eq_1
