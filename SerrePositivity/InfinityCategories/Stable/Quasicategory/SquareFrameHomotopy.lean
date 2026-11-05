module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.CompStruct
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
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.CategoryTheory.NatTrans
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Subfunctor.Basic
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Notation
public import SerrePositivity.InfinityCategories.Core.EquivalencePath
public import SerrePositivity.InfinityCategories.Core.InvertibleEdgeLifting
public import SerrePositivity.InfinityCategories.Core.SimplicialHomotopyEquivalence
public import SerrePositivity.InfinityCategories.Core.TerminalVertices
public import SerrePositivity.InfinityCategories.Core.Quasicategory.SquareFrameBoundary

/-!
分割で生成：docstring を書き直すこと
概要：四辺の指定ホモトピーを、元の円柱を保つ境界 path の全族へ貼る。
方針：可逆な成分を持つ各円柱を可逆 path の圏へ入れ、角での厳密な一致を使う。
規約：全四辺の輸送を保持する。使われ方：BF 合成二脚への正方形全体の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.LocalizingInvariants.SquareFrameHomotopy
end SerrePositivity.KST.LocalizingInvariants.SquareFrameHomotopy
namespace SerrePositivity.InfinityCategories.Stable.Quasicategory
open SerrePositivity.KST.LocalizingInvariants

structure SquareFrameHomotopy {X : SSet.{u}} (f g : SquareFrame X) where
  bottom : SSet.Homotopy f.bottom g.bottom
  top : SSet.Homotopy f.top g.top
  left : SSet.Homotopy f.left g.left
  right : SSet.Homotopy f.right g.right
  lower_left : (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u})) ≫ bottom.h =
    (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u})) ≫ left.h
  lower_right : (stdSimplex.δ (0 : Fin 2) ▷ (Δ[1] : SSet.{u})) ≫ bottom.h =
    (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u})) ≫ right.h
  upper_left : (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u})) ≫ top.h =
    (stdSimplex.δ (0 : Fin 2) ▷ (Δ[1] : SSet.{u})) ≫ left.h
  upper_right : (stdSimplex.δ (0 : Fin 2) ▷ (Δ[1] : SSet.{u})) ≫ top.h =
    (stdSimplex.δ (0 : Fin 2) ▷ (Δ[1] : SSet.{u})) ≫ right.h
  bottom_invertible : ∀ x, IsInvertibleEdge (simplicialHomotopyVertexEdge bottom x).toTruncated
  top_invertible : ∀ x, IsInvertibleEdge (simplicialHomotopyVertexEdge top x).toTruncated
  left_invertible : ∀ x, IsInvertibleEdge (simplicialHomotopyVertexEdge left x).toTruncated
  right_invertible : ∀ x, IsInvertibleEdge (simplicialHomotopyVertexEdge right x).toTruncated

namespace SquareFrameHomotopy
open SerrePositivity.KST.LocalizingInvariants.SquareFrameHomotopy
variable {X : SSet.{u}} {f g : SquareFrame X} (H : SquareFrameHomotopy f g)

local instance instMonoSSetEquivalencePathι : Mono (equivalencePathι X) := by
  unfold equivalencePathι
  infer_instance

end SquareFrameHomotopy
end SerrePositivity.InfinityCategories.Stable.Quasicategory

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrameHomotopy (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrameHomotopy := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrameHomotopy

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrameHomotopy._sizeOf_1 (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrameHomotopy._sizeOf_1 := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrameHomotopy._sizeOf_1

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrameHomotopy._sizeOf_inst (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrameHomotopy._sizeOf_inst := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrameHomotopy._sizeOf_inst

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrameHomotopy.bottom (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrameHomotopy.bottom := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrameHomotopy.bottom

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrameHomotopy.bottom_invertible := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrameHomotopy.bottom_invertible

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrameHomotopy.casesOn (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrameHomotopy.casesOn := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrameHomotopy.casesOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrameHomotopy.ctorIdx (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrameHomotopy.ctorIdx := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrameHomotopy.ctorIdx

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrameHomotopy.instMonoSSetEquivalencePathι := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrameHomotopy.instMonoSSetEquivalencePathι

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrameHomotopy.left (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrameHomotopy.left := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrameHomotopy.left

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrameHomotopy.left_invertible := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrameHomotopy.left_invertible

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrameHomotopy.lower_left := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrameHomotopy.lower_left

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrameHomotopy.lower_right := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrameHomotopy.lower_right

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrameHomotopy.mk (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrameHomotopy.mk := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrameHomotopy.mk

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrameHomotopy.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrameHomotopy.noConfusion := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrameHomotopy.noConfusion

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrameHomotopy.noConfusionType (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrameHomotopy.noConfusionType := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrameHomotopy.noConfusionType

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrameHomotopy.rec (since := "2026-11-05"), elab_as_elim]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrameHomotopy.rec := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrameHomotopy.rec

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrameHomotopy.recOn (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrameHomotopy.recOn := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrameHomotopy.recOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrameHomotopy.right (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrameHomotopy.right := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrameHomotopy.right

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrameHomotopy.right_invertible := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrameHomotopy.right_invertible

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrameHomotopy.top (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrameHomotopy.top := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrameHomotopy.top

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrameHomotopy.top_invertible := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrameHomotopy.top_invertible

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrameHomotopy.upper_left := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrameHomotopy.upper_left

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrameHomotopy.upper_right := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrameHomotopy.upper_right

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrameHomotopy.mk._flat_ctor (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrameHomotopy.mk._flat_ctor := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrameHomotopy.mk._flat_ctor

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrameHomotopy.mk.inj := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrameHomotopy.mk.inj

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrameHomotopy.mk.injEq := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrameHomotopy.mk.injEq

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrameHomotopy.mk.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrameHomotopy.mk.noConfusion := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrameHomotopy.mk.noConfusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.SquareFrameHomotopy.mk.sizeOf_spec := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrameHomotopy.mk.sizeOf_spec
