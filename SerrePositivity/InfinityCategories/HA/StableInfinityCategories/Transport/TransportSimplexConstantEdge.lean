module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
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
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpacePiZero
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.NerveCone
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.SimplexDomains
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.SimplexFirstVertex
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.SimplexFirstVertexNaturality
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.SimplexSectionDiagram
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic

/-!
分割で生成：docstring を書き直すこと
 # 初頂点を保つ射の元の底での定値区間と両端
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport
open _root_.SerrePositivity.KST.Fibration

/-- 初頂点を保つ射の区間は、元の底の同じ初頂点に厳密に定値。 -/
theorem transportSimplexFirstVertexMap_interval_constant {B : SSet.{u}}
    {c d : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory B} (f : c ⟶ d) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexPreservesFirst f) :
    yonedaEquiv.symm (nerve.edgeMk f).edge ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap B =
      SSet.const ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap B).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c)) := by
  apply yonedaEquiv.injective
  rw [yonedaEquiv_comp, Equiv.apply_symm_apply]
  refine (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap_edge_of_preservesFirst f hf).trans ?_
  change B.σ 0 _ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant _ 1
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one _).symm

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.transportSimplexFirstVertexMap_interval_constant := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.transportSimplexFirstVertexMap_interval_constant
