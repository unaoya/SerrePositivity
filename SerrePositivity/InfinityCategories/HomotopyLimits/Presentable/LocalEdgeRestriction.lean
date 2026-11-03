module

public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.EquivalenceCalculus
public import SerrePositivity.InfinityCategories.Core.InnerFiber
public import SerrePositivity.InfinityCategories.Core.InvertibleEdgeLifting
public import SerrePositivity.InfinityCategories.Core.KanFibrationEquivalence
public import SerrePositivity.InfinityCategories.Core.KanHomotopyEquivalence
public import SerrePositivity.InfinityCategories.Core.PrecompositionTensor
public import SerrePositivity.InfinityCategories.Core.RightFibration
public import SerrePositivity.InfinityCategories.Core.Slice
public import SerrePositivity.InfinityCategories.Core.Terminal
public import SerrePositivity.InfinityCategories.Core.TrivialFibrationEquivalence
public import SerrePositivity.InfinityCategories.Core.VertexFiber
public import SerrePositivity.InfinityCategories.F1.CoconeMappingRestriction
public import SerrePositivity.InfinityCategories.F1.Fibrations.CartesianFibration
public import SerrePositivity.InfinityCategories.F1.Joins.CosliceTriangleFiber
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.CosliceFiberDiagramChange
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalMappingSpace
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.LeftIntervalEquivalence
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.MappingSpaceIntervalComparison
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.PreFiberKan
public import SerrePositivity.InfinityCategories.F1B.MappingSpaces.IntervalComposition
public import SerrePositivity.InfinityCategories.HomotopyLimits.Presentable.LocalObjects
public import SerrePositivity.InfinityCategories.HomotopyLimits.CocartesianIntervalPrecomposition
public import SerrePositivity.InfinityCategories.HomotopyLimits.EdgeCosliceIntervalMap
public import SerrePositivity.InfinityCategories.HomotopyLimits.ReflectiveInvertedHom

/-!
概要：元の辺への局所性と、終点固定の coslice 制限の自明 Kan 性を照合する。
方針：三角形の全パラメータの合成比較と、始点制限の Kan fibration 性を使う。
規約：指定辺集合と元の辺を保持。使われ方：HTT 5.5.4.5 の pushout 条件。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {X : SSet.{u}} [Quasicategory X]

/-- 区間模型への比較が同値である条件を、元の coslice 制限の同値性へ戻す。 -/
lemma edgeCosliceIntervalMap_equivalence_iff_restriction
    (e : (Δ[1] : SSet.{u}) ⟶ X) (z : X _⦋0⦌) (j : Fin 2) :
    IsQCatEquivalence (edgeCosliceIntervalMap e z j) ↔
      IsQCatEquivalence (cosliceRestrictionFiberMap e (stdSimplex.δ j) z) := by
  let k := (cosliceFiberDiagramIso
    (Equiv.symm_apply_apply SSet.yonedaEquiv (stdSimplex.δ j ≫ e)).symm z).hom ≫
      cosliceFiberToIntervalMappingSpace _ z
  have hk : IsQCatEquivalence k :=
    (qCatEquivalenceOfIso (cosliceFiberDiagramIso
      (Equiv.symm_apply_apply SSet.yonedaEquiv (stdSimplex.δ j ≫ e)).symm z)).isQCatEquivalence.comp
      (cosliceFiberToIntervalMappingSpace_isQCatEquivalence _ z)
  exact ⟨fun h ↦ hk.cancel_right h, fun h ↦ h.comp hk⟩

/-- 元の辺への局所性は、終点固定余錐の始点制限の同値性と一致。 -/
lemma isLocalForHom_edge_iff_sourceRestriction (e : (Δ[1] : SSet.{u}) ⟶ X)
    (z : X _⦋0⦌) :
    IsLocalForHom (SSet.Truncated.HomotopyCategory.homMk (edgeCosliceEdge e)) z ↔
      IsQCatEquivalence (cosliceRestrictionFiberMap e (stdSimplex.δ (1 : Fin 2)) z) := by
  rw [isLocalForHom_iff_interval]
  obtain ⟨H⟩ := edgeCosliceIntervalMap_precompose e z
  have ht := edgeCosliceIntervalMap_target_isQCatEquivalence e z
  rw [← edgeCosliceIntervalMap_equivalence_iff_restriction]
  constructor
  · intro hf
    exact (ht.comp hf).ofFunctorIso (functorIsoOfSimplicialHomotopy H)
  · intro hs
    exact ht.cancel_left (hs.ofFunctorIso (functorIsoOfSimplicialHomotopy H).symm)

/-- 元の辺への局所性は、終点固定の始点制限の全境界充填性と一致。 -/
lemma isLocalForHom_edge_iff_sourceRestriction_trivial (e : (Δ[1] : SSet.{u}) ⟶ X)
    (z : X _⦋0⦌) :
    IsLocalForHom (SSet.Truncated.HomotopyCategory.homMk (edgeCosliceEdge e)) z ↔
      TrivialKanFibration (cosliceRestrictionFiberMap e (stdSimplex.δ (1 : Fin 2)) z) := by
  rw [isLocalForHom_edge_iff_sourceRestriction]
  constructor
  · intro h
    have := coconeMappingSpace_restrict_fibration e (stdSimplex.δ (1 : Fin 2)) z
    exact trivialKanFibration_of_fibration_of_isQCatEquivalence _ h
  · intro h
    have := h
    exact isQCatEquivalence_of_trivialKanFibration _

/-- 指定辺集合の元の辺に対し、局所対象への余錐の始点制限は自明 Kan 射。 -/
lemma sourceRestriction_trivial_of_localObject (W : Set (X _⦋1⦌))
    (e : (Δ[1] : SSet.{u}) ⟶ X) (he : SSet.yonedaEquiv e ∈ W)
    {z : X _⦋0⦌} (hz : IsLocalObject W z) :
    TrivialKanFibration (cosliceRestrictionFiberMap e (stdSimplex.δ (1 : Fin 2)) z) := by
  apply (isLocalForHom_edge_iff_sourceRestriction_trivial e z).mp
  apply (isLocalForHom_homMk_iff_edgeOfSimplex (edgeCosliceEdge e) z).mpr
  exact hz _ he

end
end SerrePositivity.InfinityCategories.HomotopyLimits
