module
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic

/-!
概要：標準区間の二つの端点を指定する単射。
方針：二点の定値単体集合から標準区間の定値単体へ送る。
規約：指定された三角形と同型の値を保持する。
使われ方：引き戻し錐と指定 path の比較を簡約する。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

/-- 概要：標準区間の二つの端点を指定する単射。
方針：二点の定値単体集合から標準区間の定値単体へ送る。
規約：端点の順は始点・終点を保つ。
使われ方：Tamme の lax pullback の構成と普遍性。 -/
def arrowBoundary : SSet.{u} :=
  (CategoryTheory.Functor.const SimplexCategoryᵒᵖ).obj (ULift.{u} (Fin 2))
/-- 概要：標準区間の二つの端点を指定する単射。
方針：二点の定値単体集合から標準区間の定値単体へ送る。
規約：端点の順は始点・終点を保つ。
使われ方：Tamme の lax pullback の構成と普遍性。 -/
lemma arrowBoundary_constant (i : ULift.{u} (Fin 2)) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (X := arrowBoundary) i n = i := rfl
/-- 概要：標準区間の二つの端点を指定する単射。
方針：二点の定値単体集合から標準区間の定値単体へ送る。
規約：端点の順は始点・終点を保つ。
使われ方：Tamme の lax pullback の構成と普遍性。 -/
def arrowBoundaryι : arrowBoundary.{u} ⟶ (Δ[1] : SSet.{u}) where
  app d := ↾fun i ↦ stdSimplex.const 1 i.down d
  naturality d e α := by
    apply ConcreteCategory.hom_ext
    intro i
    rfl
/-- 概要：標準区間の二つの端点を指定する単射。
方針：二点の定値単体集合から標準区間の定値単体へ送る。
規約：端点の順は始点・終点を保つ。
使われ方：Tamme の lax pullback の構成と普遍性。 -/
instance arrowBoundaryι_mono : Mono (arrowBoundaryι.{u}) := by
  rw [NatTrans.mono_iff_mono_app]
  intro d
  rw [mono_iff_injective]
  intro i j h
  apply ULift.ext
  exact congrArg (fun s ↦ ((stdSimplex.objEquiv s).toOrderHom) 0) h

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
