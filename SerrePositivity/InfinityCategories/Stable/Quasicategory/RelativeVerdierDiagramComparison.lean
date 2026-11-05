module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.HomotopyCat
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Opposite
public import Mathlib.CategoryTheory.Category.Basic
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
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Logic.Equiv.Defs
public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.PastingShapes
public import SerrePositivity.InfinityCategories.Core.Pullback
public import SerrePositivity.InfinityCategories.Core.PushoutShape
public import SerrePositivity.InfinityCategories.Stable.Infinity.StableInfinity
public import SerrePositivity.InfinityCategories.Stable.Quasicategory.RelativeInvariant
public import SerrePositivity.InfinityCategories.Stable.Quasicategory.RelativeVerdierPullback

/-!
分割で生成：docstring を書き直すこと
概要：相対 Verdier 図式の全比較を、包含・商・零角の指定比較に固定する。
方針：境界比較を先に指定し、全図式同型の制限との一致を型に含める。
規約：ν 像の同型から S 内の厳密代表の存在を推論しない。
使われ方：K-S• の長方形と K-B の相対懸垂屋根の比較接続口。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.LocalizingInvariants.RelativeVerdierRectangle
end SerrePositivity.KST.LocalizingInvariants.RelativeVerdierRectangle
namespace SerrePositivity.InfinityCategories.Stable.Quasicategory
open SerrePositivity.KST.LocalizingInvariants

/-- Verdier 四角形の零角 (0,1) の指定包含。 -/
def verdierZeroCorner : (Δ[0] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1] :=
  SSet.yonedaEquiv.symm
    (stdSimplex.obj₀Equiv.symm (0 : Fin 2), stdSimplex.obj₀Equiv.symm (1 : Fin 2))

/-- 呼出側が先に指定する包含辺・商辺・零角の比較。零角の同一視は等号に限定しない。 -/
structure VerdierSquareBoundaryIso {X : SSet.{u}}
    (F G : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X) where
  inclusion : FunctorIso (squareBottomEdge ≫ F) (squareBottomEdge ≫ G)
  quotient : FunctorIso (squareRightEdge ≫ F) (squareRightEdge ≫ G)
  zero : FunctorIso (verdierZeroCorner ≫ F) (verdierZeroCorner ≫ G)

/-- 全図式比較は、三つの指定境界比較そのものを制限として持つ。 -/
structure VerdierSquareDiagramIso {X : SSet.{u}}
    (F G : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X) (b : VerdierSquareBoundaryIso F G) where
  comparison : FunctorIso F G
  inclusion_eq : comparison.precomp squareBottomEdge = b.inclusion
  quotient_eq : comparison.precomp squareRightEdge = b.quotient
  zero_eq : comparison.precomp verdierZeroCorner = b.zero

/-- 右面・外周の転置 Verdier 面。j=0 は右面、j=1 は外周。 -/
def verdierRectangleFace (j : Fin 2) :
    (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ Δ[2] ⊗ Δ[1] :=
  (β_ _ _).hom ≫ (stdSimplex.δ (j.castSucc : Fin 3) ▷ Δ[1])

/-- 二つの Verdier 面の境界と、上下の指定合成三角形の比較。 -/
structure VerdierRectangleBoundaryIso {X : SSet.{u}}
    (F G : (Δ[2] ⊗ Δ[1] : SSet.{u}) ⟶ X) where
  faces (j : Fin 2) : VerdierSquareBoundaryIso
    (verdierRectangleFace j ≫ F) (verdierRectangleFace j ≫ G)
  bottom : FunctorIso (pastingBottomTriangle F) (pastingBottomTriangle G)
  top : FunctorIso (pastingTopTriangle F) (pastingTopTriangle G)

/-- 全長方形の同型。二面の指定三境界と上下の二単体を同時に保持する。 -/
structure VerdierRectangleDiagramIso {X : SSet.{u}}
    (F G : (Δ[2] ⊗ Δ[1] : SSet.{u}) ⟶ X) (b : VerdierRectangleBoundaryIso F G) where
  comparison : FunctorIso F G
  faces (j : Fin 2) : VerdierSquareDiagramIso
    (verdierRectangleFace j ≫ F) (verdierRectangleFace j ≫ G) (b.faces j)
  faces_eq (j : Fin 2) : comparison.precomp (verdierRectangleFace j) = (faces j).comparison
  bottom_eq : comparison.precomp (pastingBottomTriangle (𝟙 _)) = b.bottom
  top_eq : comparison.precomp (pastingTopTriangle (𝟙 _)) = b.top

namespace RelativeVerdierRectangle
open SerrePositivity.KST.LocalizingInvariants.RelativeVerdierRectangle
variable {S : SSet.{u + 1}} {ν : S ⟶ StableInfinity.{u}}

/-- 実 ν 像の二つの ofSquare 認証を、その同じ源長方形に貼る。 -/
def ofActualFaces (F : (Δ[2] ⊗ Δ[1] : SSet.{u + 1}) ⟶ S)
    (r o : RelativeVerdierDiagram ν)
    (hr : r.square = verdierRectangleFace 0 ≫ F)
    (ho : o.square = verdierRectangleFace 1 ≫ F) : RelativeVerdierRectangle ν where
  diagram := F
  right := r
  outer := o
  right_eq := by
    rw [hr]
    change _ = (β_ (Δ[1] : SSet.{u + 1}) Δ[1]).hom ≫
      (β_ (Δ[1] : SSet.{u + 1}) Δ[1]).hom ≫ pastingSquare F 0
    rw [← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]
  outer_eq := by
    rw [ho]
    change _ = (β_ (Δ[1] : SSet.{u + 1}) Δ[1]).hom ≫
      (β_ (Δ[1] : SSet.{u + 1}) Δ[1]).hom ≫ pastingSquare F 1
    rw [← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]

end RelativeVerdierRectangle
end SerrePositivity.InfinityCategories.Stable.Quasicategory

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierRectangleBoundaryIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRectangleBoundaryIso := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierRectangleBoundaryIso

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierRectangleDiagramIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRectangleDiagramIso := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierRectangleDiagramIso

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierSquareBoundaryIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierSquareBoundaryIso := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierSquareBoundaryIso

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierSquareDiagramIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierSquareDiagramIso := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierSquareDiagramIso

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.verdierRectangleFace (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierRectangleFace := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.verdierRectangleFace

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.verdierZeroCorner (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierZeroCorner := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.verdierZeroCorner

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.RelativeVerdierRectangle.ofActualFaces (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativeVerdierRectangle.ofActualFaces := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.RelativeVerdierRectangle.ofActualFaces

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierRectangleBoundaryIso._sizeOf_1 (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRectangleBoundaryIso._sizeOf_1 := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierRectangleBoundaryIso._sizeOf_1

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierRectangleBoundaryIso._sizeOf_inst (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRectangleBoundaryIso._sizeOf_inst := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierRectangleBoundaryIso._sizeOf_inst

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierRectangleBoundaryIso.bottom (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRectangleBoundaryIso.bottom := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierRectangleBoundaryIso.bottom

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierRectangleBoundaryIso.casesOn (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRectangleBoundaryIso.casesOn := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierRectangleBoundaryIso.casesOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierRectangleBoundaryIso.ctorIdx (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRectangleBoundaryIso.ctorIdx := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierRectangleBoundaryIso.ctorIdx

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierRectangleBoundaryIso.faces (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRectangleBoundaryIso.faces := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierRectangleBoundaryIso.faces

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierRectangleBoundaryIso.mk (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRectangleBoundaryIso.mk := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierRectangleBoundaryIso.mk

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierRectangleBoundaryIso.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRectangleBoundaryIso.noConfusion := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierRectangleBoundaryIso.noConfusion

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierRectangleBoundaryIso.noConfusionType (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRectangleBoundaryIso.noConfusionType := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierRectangleBoundaryIso.noConfusionType

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierRectangleBoundaryIso.rec (since := "2026-11-05"), elab_as_elim]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRectangleBoundaryIso.rec := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierRectangleBoundaryIso.rec

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierRectangleBoundaryIso.recOn (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRectangleBoundaryIso.recOn := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierRectangleBoundaryIso.recOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierRectangleBoundaryIso.top (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRectangleBoundaryIso.top := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierRectangleBoundaryIso.top

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierRectangleDiagramIso._sizeOf_1 (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRectangleDiagramIso._sizeOf_1 := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierRectangleDiagramIso._sizeOf_1

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierRectangleDiagramIso._sizeOf_inst (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRectangleDiagramIso._sizeOf_inst := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierRectangleDiagramIso._sizeOf_inst

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRectangleDiagramIso.bottom_eq := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierRectangleDiagramIso.bottom_eq

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierRectangleDiagramIso.casesOn (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRectangleDiagramIso.casesOn := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierRectangleDiagramIso.casesOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierRectangleDiagramIso.comparison (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRectangleDiagramIso.comparison := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierRectangleDiagramIso.comparison

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierRectangleDiagramIso.ctorIdx (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRectangleDiagramIso.ctorIdx := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierRectangleDiagramIso.ctorIdx

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierRectangleDiagramIso.faces (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRectangleDiagramIso.faces := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierRectangleDiagramIso.faces

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRectangleDiagramIso.faces_eq := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierRectangleDiagramIso.faces_eq

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierRectangleDiagramIso.mk (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRectangleDiagramIso.mk := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierRectangleDiagramIso.mk

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierRectangleDiagramIso.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRectangleDiagramIso.noConfusion := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierRectangleDiagramIso.noConfusion

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierRectangleDiagramIso.noConfusionType (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRectangleDiagramIso.noConfusionType := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierRectangleDiagramIso.noConfusionType

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierRectangleDiagramIso.rec (since := "2026-11-05"), elab_as_elim]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRectangleDiagramIso.rec := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierRectangleDiagramIso.rec

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierRectangleDiagramIso.recOn (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRectangleDiagramIso.recOn := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierRectangleDiagramIso.recOn

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRectangleDiagramIso.top_eq := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierRectangleDiagramIso.top_eq

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierSquareBoundaryIso._sizeOf_1 (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierSquareBoundaryIso._sizeOf_1 := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierSquareBoundaryIso._sizeOf_1

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierSquareBoundaryIso._sizeOf_inst (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierSquareBoundaryIso._sizeOf_inst := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierSquareBoundaryIso._sizeOf_inst

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierSquareBoundaryIso.casesOn (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierSquareBoundaryIso.casesOn := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierSquareBoundaryIso.casesOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierSquareBoundaryIso.ctorIdx (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierSquareBoundaryIso.ctorIdx := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierSquareBoundaryIso.ctorIdx

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierSquareBoundaryIso.inclusion (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierSquareBoundaryIso.inclusion := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierSquareBoundaryIso.inclusion

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierSquareBoundaryIso.mk (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierSquareBoundaryIso.mk := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierSquareBoundaryIso.mk

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierSquareBoundaryIso.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierSquareBoundaryIso.noConfusion := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierSquareBoundaryIso.noConfusion

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierSquareBoundaryIso.noConfusionType (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierSquareBoundaryIso.noConfusionType := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierSquareBoundaryIso.noConfusionType

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierSquareBoundaryIso.quotient (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierSquareBoundaryIso.quotient := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierSquareBoundaryIso.quotient

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierSquareBoundaryIso.rec (since := "2026-11-05"), elab_as_elim]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierSquareBoundaryIso.rec := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierSquareBoundaryIso.rec

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierSquareBoundaryIso.recOn (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierSquareBoundaryIso.recOn := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierSquareBoundaryIso.recOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierSquareBoundaryIso.zero (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierSquareBoundaryIso.zero := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierSquareBoundaryIso.zero

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierSquareDiagramIso._sizeOf_1 (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierSquareDiagramIso._sizeOf_1 := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierSquareDiagramIso._sizeOf_1

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierSquareDiagramIso._sizeOf_inst (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierSquareDiagramIso._sizeOf_inst := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierSquareDiagramIso._sizeOf_inst

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierSquareDiagramIso.casesOn (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierSquareDiagramIso.casesOn := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierSquareDiagramIso.casesOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierSquareDiagramIso.comparison (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierSquareDiagramIso.comparison := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierSquareDiagramIso.comparison

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierSquareDiagramIso.ctorIdx (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierSquareDiagramIso.ctorIdx := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierSquareDiagramIso.ctorIdx

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierSquareDiagramIso.inclusion_eq := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierSquareDiagramIso.inclusion_eq

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierSquareDiagramIso.mk (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierSquareDiagramIso.mk := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierSquareDiagramIso.mk

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierSquareDiagramIso.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierSquareDiagramIso.noConfusion := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierSquareDiagramIso.noConfusion

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierSquareDiagramIso.noConfusionType (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierSquareDiagramIso.noConfusionType := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierSquareDiagramIso.noConfusionType

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierSquareDiagramIso.quotient_eq := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierSquareDiagramIso.quotient_eq

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierSquareDiagramIso.rec (since := "2026-11-05"), elab_as_elim]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierSquareDiagramIso.rec := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierSquareDiagramIso.rec

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierSquareDiagramIso.recOn (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierSquareDiagramIso.recOn := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierSquareDiagramIso.recOn

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierSquareDiagramIso.zero_eq := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierSquareDiagramIso.zero_eq

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierZeroCorner._proof_1 := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.verdierZeroCorner._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativeVerdierRectangle.ofActualFaces._proof_1 := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.RelativeVerdierRectangle.ofActualFaces._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.RelativeVerdierRectangle.ofActualFaces._proof_2 := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.RelativeVerdierRectangle.ofActualFaces._proof_2

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierRectangleBoundaryIso.mk._flat_ctor (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRectangleBoundaryIso.mk._flat_ctor := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierRectangleBoundaryIso.mk._flat_ctor

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRectangleBoundaryIso.mk.inj := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierRectangleBoundaryIso.mk.inj

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRectangleBoundaryIso.mk.injEq := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierRectangleBoundaryIso.mk.injEq

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierRectangleBoundaryIso.mk.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRectangleBoundaryIso.mk.noConfusion := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierRectangleBoundaryIso.mk.noConfusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRectangleBoundaryIso.mk.sizeOf_spec := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierRectangleBoundaryIso.mk.sizeOf_spec

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierRectangleDiagramIso.mk._flat_ctor (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRectangleDiagramIso.mk._flat_ctor := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierRectangleDiagramIso.mk._flat_ctor

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRectangleDiagramIso.mk.inj := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierRectangleDiagramIso.mk.inj

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRectangleDiagramIso.mk.injEq := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierRectangleDiagramIso.mk.injEq

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierRectangleDiagramIso.mk.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRectangleDiagramIso.mk.noConfusion := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierRectangleDiagramIso.mk.noConfusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRectangleDiagramIso.mk.sizeOf_spec := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierRectangleDiagramIso.mk.sizeOf_spec

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierSquareBoundaryIso.mk._flat_ctor (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierSquareBoundaryIso.mk._flat_ctor := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierSquareBoundaryIso.mk._flat_ctor

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierSquareBoundaryIso.mk.inj := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierSquareBoundaryIso.mk.inj

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierSquareBoundaryIso.mk.injEq := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierSquareBoundaryIso.mk.injEq

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierSquareBoundaryIso.mk.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierSquareBoundaryIso.mk.noConfusion := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierSquareBoundaryIso.mk.noConfusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierSquareBoundaryIso.mk.sizeOf_spec := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierSquareBoundaryIso.mk.sizeOf_spec

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierSquareDiagramIso.mk._flat_ctor (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierSquareDiagramIso.mk._flat_ctor := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierSquareDiagramIso.mk._flat_ctor

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierSquareDiagramIso.mk.inj := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierSquareDiagramIso.mk.inj

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierSquareDiagramIso.mk.injEq := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierSquareDiagramIso.mk.injEq

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierSquareDiagramIso.mk.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierSquareDiagramIso.mk.noConfusion := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierSquareDiagramIso.mk.noConfusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierSquareDiagramIso.mk.sizeOf_spec := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.VerdierSquareDiagramIso.mk.sizeOf_spec
