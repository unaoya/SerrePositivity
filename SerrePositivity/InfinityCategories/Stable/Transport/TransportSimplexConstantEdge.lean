module
public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.CompStruct
public import Mathlib.AlgebraicTopology.SimplicialSet.CompStructTruncated
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Opposite
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.ComposableArrows.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.NatTrans
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Logic.Equiv.Defs
public import SerrePositivity.InfinityCategories.Core.MappingSpacePiZero
public import SerrePositivity.InfinityCategories.Core.NerveCone
public import SerrePositivity.InfinityCategories.F1.Transport.SimplexDomains
public import SerrePositivity.InfinityCategories.F1.Transport.SimplexFirstVertex
public import SerrePositivity.InfinityCategories.F1.Transport.SimplexFirstVertexNaturality
public import SerrePositivity.InfinityCategories.F1.Transport.SimplexSectionDiagram
public import SerrePositivity.InfinityCategories.PinchedHom.Basic

/-!
分割で生成：docstring を書き直すこと
 # 初頂点を保つ射の元の底での定値区間と両端
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration

/-- 初頂点を保つ射の区間は、元の底の同じ初頂点に厳密に定値。 -/
theorem transportSimplexFirstVertexMap_interval_constant {B : SSet.{u}}
    {c d : TransportSimplexCategory B} (f : c ⟶ d) (hf : TransportSimplexPreservesFirst f) :
    yonedaEquiv.symm (nerve.edgeMk f).edge ≫ transportSimplexFirstVertexMap B =
      SSet.const ((transportSimplexFirstVertexMap B).app (Opposite.op ⦋0⦌) (nerveVertex c)) := by
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp, Equiv.apply_symm_apply]
  refine (transportSimplexFirstVertexMap_edge_of_preservesFirst f hf).trans ?_
  change B.σ 0 _ = PinchedHom.constant _ 1
  exact (pinchedConstant_one _).symm

end SerrePositivity.KST.Fibration
