module
public import Mathlib.AlgebraicTopology.RelativeCellComplex.Basic
public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
public import Mathlib.AlgebraicTopology.SimplicialSet.Finite
public import Mathlib.AlgebraicTopology.SimplicialSet.Horn
public import Mathlib.AlgebraicTopology.SimplicialSet.Monomorphisms
public import Mathlib.AlgebraicTopology.SimplicialSet.Presentable
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
public import Mathlib.Basic.Logic.Basic
public import Mathlib.Basic.Opposite
public import Mathlib.Basic.UnivLE
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.Discrete.Basic
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Filtered
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.WalkingPair
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
public import Mathlib.CategoryTheory.Limits.Shapes.Preorder.HasIterationOfShape
public import Mathlib.CategoryTheory.Limits.Shapes.Preorder.TransfiniteCompositionOfShape
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.MorphismProperty.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.MorphismProperty.IsSmall
public import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.MorphismProperty.Retract
public import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Presentable.Basic
public import Mathlib.CategoryTheory.Presentable.Finite
public import Mathlib.CategoryTheory.SmallObject.Basic
public import Mathlib.CategoryTheory.SmallObject.IsCardinalForSmallObjectArgument
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Set.CoeSort
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.BourbakiWitt
public import Mathlib.Order.CompleteBooleanAlgebra
public import Mathlib.Order.CompleteLattice.Defs
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.ConditionallyCompletePartialOrder.Defs
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Directed
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Order.Lattice
public import Mathlib.Order.RelIso.Basic
public import Mathlib.Order.Shrink
public import Mathlib.SetTheory.Cardinal.Defs
public import Mathlib.SetTheory.Cardinal.Regular
public import Mathlib.SetTheory.Ordinal.Arithmetic
public import Mathlib.SetTheory.Ordinal.Basic
public import SerrePositivity.HomotopicalAlgebra.Simplicial.GeneratedLeftClass
public import Mathlib.Tactic.CrossRefAttribute


/-! # Concrete smallness of the fixed simplicial generating maps

The boundary and horn domains have the same aleph-zero presentability bound
in the SSet hom-universe. These statements do not assume a completed
Kan-Quillen model structure, nor introduce a weak-equivalence class.
-/

@[expose] public section
universe u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen
namespace SerrePositivity.SimplicialModel
open SSet SSet.modelCategoryQuillen
attribute [local instance] Cardinal.fact_isRegular_aleph0
attribute [local instance] Cardinal.orderBotAleph0OrdToType
lemma boundaryGenerator_domain_presentable {A B : SSet.{u}} (f : A ⟶ B) (hf : I f) :
    IsCardinalPresentable A Cardinal.aleph0.{u} := by
  rcases hf with ⟨n⟩
  infer_instance

lemma hornGenerator_domain_presentable {A B : SSet.{u}} (f : A ⟶ B) (hf : J f) :
    IsCardinalPresentable A Cardinal.aleph0.{u} := by
  simp only [J, MorphismProperty.iSup_iff] at hf
  obtain ⟨n, ⟨i⟩⟩ := hf
  infer_instance

lemma boundaryGenerators_isSmall : I.{u}.IsSmall.{u} := by
  exact MorphismProperty.isSmall_ofHoms _

lemma boundaryGenerators_cardinal :
    MorphismProperty.IsCardinalForSmallObjectArgument I.{u} Cardinal.aleph0.{u} := by
  let : I.{u}.IsSmall.{u} := boundaryGenerators_isSmall
  refine { preservesColimit := ?_ }
  intro A B X Y f hf g hg
  have : IsCardinalPresentable A Cardinal.aleph0.{u} := boundaryGenerator_domain_presentable f hf
  infer_instance

/-- The source boundary generators themselves have the small-object argument. -/
lemma boundaryGenerators_smallObjectArgument : I.{u}.HasSmallObjectArgument.{u} := by
  let : MorphismProperty.IsCardinalForSmallObjectArgument I.{u} Cardinal.aleph0.{u} :=
    boundaryGenerators_cardinal
  exact ⟨Cardinal.aleph0, inferInstance, inferInstance, inferInstance⟩

/-- The source horn small-object argument is reused from the fixed Mathlib. -/
lemma hornGenerators_smallObjectArgument : J.{u}.HasSmallObjectArgument.{u} := inferInstance

/-- Boundary generation recovers precisely the actual monomorphisms, without
assuming a weak-equivalence class or the Kan–Quillen model axioms. -/
@[kerodon 0077]
lemma boundaryGenerators_leftClass : I.{u}.rlp.llp = MorphismProperty.monomorphisms SSet.{u} := by
  let : I.{u}.HasSmallObjectArgument.{u} := boundaryGenerators_smallObjectArgument
  apply le_antisymm
  · apply SerrePositivity.ModelGeneration.generatedLeft_le_of_cells_le
    have hc : MorphismProperty.coproducts.{u} I.{u} ≤
        MorphismProperty.monomorphisms SSet.{u} :=
      MorphismProperty.coproducts_le_iff.2 I_le_monomorphisms
    have hp : (MorphismProperty.coproducts.{u} I.{u}).pushouts ≤
        MorphismProperty.monomorphisms SSet.{u} :=
      MorphismProperty.pushouts_le_iff.2 hc
    exact MorphismProperty.transfiniteCompositions_le_iff.{u}.2 hp
  · rw [← SSet.rlp_monomorphisms]
    exact MorphismProperty.le_llp_rlp _

end SerrePositivity.SimplicialModel
