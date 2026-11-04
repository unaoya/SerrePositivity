module

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
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

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
end SerrePositivity.KST.LocalizingInvariants
