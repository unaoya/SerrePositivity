module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import Mathlib.AlgebraicTopology.Quasicategory.Basic
public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.CompStruct
public import Mathlib.AlgebraicTopology.SimplicialSet.CompStructTruncated
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Opposite
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Iso
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Category
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
public import Mathlib.Logic.Equiv.Defs
public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.InternalHomFlipAdjunction
public import SerrePositivity.InfinityCategories.Core.InternalHomSwap
public import SerrePositivity.InfinityCategories.Core.InvertibleEdgeLifting

/-!
分割で生成：docstring を書き直すこと
概要：転置された全族比較の同じ一次単体を、元のパラメータ族の core 比較へ戻す。
方針：内部 Hom 交換の実単体写像で比較辺を戻し、同じ prism の全辺反転を証明する。
規約：全関手同型の代表辺を選び直さず、指定された元の比較辺を使う。
使われ方：有限分母余錐族の比較を元の strict core 逆像の商射へ接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.Stable.Quasicategory
open SerrePositivity.KST.LocalizingInvariants

/-- 転置した全族の指定比較辺を、一次単体を選び直さず元の全族へ戻す。 -/
def spanFunctorEdgeUnflip {K L X : SSet.{u}} {F G : K ⟶ (ihom L).obj X}
    (l : Truncated.Edge
      (X := (truncation 2).obj ((ihom L).obj ((ihom K).obj X)))
      (functorVertex (internalHomFlipHomEquiv K L X F))
      (functorVertex (internalHomFlipHomEquiv K L X G))) :
    SSet.Edge (functorVertex F) (functorVertex G) := by
  let t := (SSet.Edge.ofTruncated l).map (internalHomSwapIso L K X).hom
  have hs (f : K ⟶ (ihom L).obj X) :
      (internalHomSwapIso L K X).hom.app (Opposite.op ⦋0⦌)
        (functorVertex (internalHomFlipHomEquiv K L X f)) = functorVertex f := by
    rw [internalHomSwapIso_functorVertex]
    change functorVertex ((internalHomFlipHomEquiv K L X).symm
      ((internalHomFlipHomEquiv K L X) f)) = _
    rw [Equiv.symm_apply_apply]
  exact t.ofEq (hs F) (hs G)

lemma spanFunctorEdgeUnflip_edge {K L X : SSet.{u}} {F G : K ⟶ (ihom L).obj X}
    (l : Truncated.Edge
      (X := (truncation 2).obj ((ihom L).obj ((ihom K).obj X)))
      (functorVertex (internalHomFlipHomEquiv K L X F))
      (functorVertex (internalHomFlipHomEquiv K L X G))) :
    (spanFunctorEdgeUnflip l).edge =
      (internalHomSwapIso L K X).hom.app (Opposite.op ⦋1⦌) l.edge := rfl

lemma spanFunctorEdgeUnflip_isInvertible {K L X : SSet.{u}} [Quasicategory X]
    {F G : K ⟶ (ihom L).obj X}
    (l : Truncated.Edge
      (X := (truncation 2).obj ((ihom L).obj ((ihom K).obj X)))
      (functorVertex (internalHomFlipHomEquiv K L X F))
      (functorVertex (internalHomFlipHomEquiv K L X G)))
    (hl : IsInvertibleEdge (X := (ihom L).obj ((ihom K).obj X)) l) :
    IsInvertibleEdge (X := (ihom K).obj ((ihom L).obj X))
      (spanFunctorEdgeUnflip l).toTruncated := by
  exact (isInvertibleEdge_congr
    (e := l.map ((truncation 2).map (internalHomSwapIso L K X).hom))
    (f := (spanFunctorEdgeUnflip l).toTruncated) rfl).mp
      (hl.map (internalHomSwapIso L K X).hom)

end SerrePositivity.InfinityCategories.Stable.Quasicategory

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.spanFunctorEdgeUnflip (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.spanFunctorEdgeUnflip := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.spanFunctorEdgeUnflip

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.spanFunctorEdgeUnflip_edge := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.spanFunctorEdgeUnflip_edge

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.spanFunctorEdgeUnflip_isInvertible := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.spanFunctorEdgeUnflip_isInvertible

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.spanFunctorEdgeUnflip._proof_1 := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.spanFunctorEdgeUnflip._proof_1
