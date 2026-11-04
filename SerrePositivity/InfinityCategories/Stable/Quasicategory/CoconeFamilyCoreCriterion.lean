module

public import Mathlib.AlgebraicTopology.Quasicategory.Basic
public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
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
public import Mathlib.Logic.Equiv.Defs
public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.EquivalencePath
public import SerrePositivity.InfinityCategories.Core.FunctorEdgePointwise
public import SerrePositivity.InfinityCategories.Core.FunctorEvaluation
public import SerrePositivity.InfinityCategories.Core.InvertibleEdgeLifting
public import SerrePositivity.InfinityCategories.F1B.Localization.Localization

/-!
分割で生成：docstring を書き直すこと
概要：余錐全族の前段と頂点の辺反転から、その同じ全族の辺反転を証明する。
方針：指定されたパラメータ辺を全図式頂点で検査し、join の二因子で尽くす。
規約：パラメータやその区間に Kan 性を仮定せず、元の実全族を変更しない。
使われ方：実分母円柱の商像を元の全図式 core へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

lemma functorFamily_invertsEdges_of_evaluations {P L X : SSet.{u}} [Quasicategory X]
    (F : P ⟶ (ihom L).obj X) (W : Set (P _⦋1⦌))
    (hF : ∀ l : L _⦋0⦌, InvertsEdges (F ≫ evaluateFunctorAt l) W) :
    InvertsEdges F W := by
  intro s hs
  let a := edgeOfSimplex (F.app (Opposite.op ⦋1⦌) s)
  let f := (functorVertexEquiv L X).symm ((ihom L).obj X |>.δ 1 (F.app (Opposite.op ⦋1⦌) s))
  let g := (functorVertexEquiv L X).symm ((ihom L).obj X |>.δ 0 (F.app (Opposite.op ⦋1⦌) s))
  let e : Truncated.Edge (X := (truncation 2).obj ((ihom L).obj X))
      (functorVertex f) (functorVertex g) :=
    ((SSet.Edge.ofTruncated a).ofEq
      ((functorVertexEquiv L X).apply_symm_apply _).symm
      ((functorVertexEquiv L X).apply_symm_apply _).symm).toTruncated
  apply (isInvertibleEdge_congr (e := e)
    (f := (edgeOfSimplex s).map ((truncation 2).map F)) rfl).mp
  apply (isInvertibleEdge_iff_evaluateFunctorAt e).mpr
  intro l
  exact (isInvertibleEdge_congr (e := e.map ((truncation 2).map (evaluateFunctorAt l)))
    (f := (edgeOfSimplex s).map ((truncation 2).map (F ≫ evaluateFunctorAt l))) rfl).mpr
      (hF l hs)

end SerrePositivity.KST.LocalizingInvariants
