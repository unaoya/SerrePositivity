module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalMappingVertexEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.PointedIntervalTransport
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.ParametrizedFiberTransportNaturality
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithful

/-!
概要：元の pointed 区間輸送を、同じパラメータの頂点が表す元の辺輸送へ接続する。
方針：全族の普遍輸送比較を評価し、同じ辺での普遍輸送の比較を続ける。
規約：評価後も始点の fiber 全体の写像を保持する。
使われ方：G8 の錐の全 Hom 作用から値の全族比較への復帰。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories
open MorphismSpaces IsomorphismsAndIsofibrations Equivalence
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding

namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces

attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 概要：同じ区間頂点への同型があれば、元の全 fiber 輸送をその辺輸送へ比較できる。
方針：元の普遍輸送との比較の後、区間頂点の同型を普遍輸送で写す。
規約：fiber の全写像間の同型。使われ方：G8 の恒等射での Hom 作用の評価。 -/
def pointedIntervalTransport_vertex_edgeIso {T : SSet.{u + 1}} [Quasicategory T]
    {x y : SpaceInfinity.{u} _⦋0⦌} (a : T ⟶ intervalMappingSpace x y)
    (v : T _⦋0⦌) (e : SpaceInfinity.{u}.Edge x y)
    (h : VertexIso (a.app _ v) (intervalMappingVertexOfEdge e)) :
    FunctorIso
      ((functorVertexEquiv _ _).symm ((pointedIntervalTransport a).map.app _ v))
      (edgeTransport pointedSpaceProjection e) := by
  let p := pointedSpaceProjection.{u}
  let U := parametrizedFiberTransport p x y
  have hc : intervalMappingCurryOfEndpoints (intervalMappingUncurry a)
      (intervalMappingUncurry_zero a) (intervalMappingUncurry_one a) = a := by
    apply intervalMappingUncurry_injective
    rw [intervalMappingUncurry_curryOfEndpoints]
  have h₀ := (pointedIntervalTransport a).mapIso_parametrized p
    (intervalMappingUncurry a) (intervalMappingUncurry_zero a) (intervalMappingUncurry_one a)
  rw [hc] at h₀
  have h₁ := h.map U
  have h₂ := parametrizedFiberTransport_at_edgeIso p e
  change VertexIso (functorVertex _) (functorVertex _) at h₂
  have h₂v : functorVertex ((functorVertexEquiv _ _).symm
      (U.app _ (intervalMappingVertexOfEdge e))) = U.app _ (intervalMappingVertexOfEdge e) :=
    (functorVertexEquiv _ _).apply_symm_apply _
  rw [h₂v] at h₂
  change VertexIso (functorVertex _) (functorVertex _)
  have hav : functorVertex ((functorVertexEquiv _ _).symm
      ((pointedIntervalTransport a).map.app _ v)) = (pointedIntervalTransport a).map.app _ v :=
    (functorVertexEquiv _ _).apply_symm_apply _
  rw [hav]
  exact h₀.app v ≪≫ h₁ ≪≫ h₂

/-- 概要：同じパラメータで評価した元の pointed 輸送は、その頂点の表す辺の輸送に同型。
方針：全族の普遍輸送比較と、同じ辺の輸送の比較を合成する。
規約：始点 fiber の全パラメータを保持。使われ方：錐の Hom 作用の評価。 -/
def pointedIntervalTransport_at_vertexIso {T : SSet.{u + 1}} [Quasicategory T]
    {x y : SpaceInfinity.{u} _⦋0⦌} (a : T ⟶ intervalMappingSpace x y) (v : T _⦋0⦌) :
    FunctorIso
      ((functorVertexEquiv _ _).symm ((pointedIntervalTransport a).map.app _ v))
      (edgeTransport pointedSpaceProjection (intervalMappingEdgeOfVertex (a.app _ v))) := by
  let p := pointedSpaceProjection.{u}
  let U := parametrizedFiberTransport p x y
  have hc : intervalMappingCurryOfEndpoints (intervalMappingUncurry a)
      (intervalMappingUncurry_zero a) (intervalMappingUncurry_one a) = a := by
    apply intervalMappingUncurry_injective
    rw [intervalMappingUncurry_curryOfEndpoints]
  have h := (pointedIntervalTransport a).mapIso_parametrized p
    (intervalMappingUncurry a) (intervalMappingUncurry_zero a) (intervalMappingUncurry_one a)
  rw [hc] at h
  have h' := h.app v
  let f := (functorVertexEquiv _ _).symm ((pointedIntervalTransport a).map.app _ v)
  let g := (functorVertexEquiv _ _).symm (U.app _ (a.app _ v))
  have hf : functorVertex f = (pointedIntervalTransport a).map.app _ v :=
    (functorVertexEquiv _ _).apply_symm_apply _
  have hg : functorVertex g = U.app _ (a.app _ v) :=
    (functorVertexEquiv _ _).apply_symm_apply _
  have hi : FunctorIso f g := by
    change VertexIso (functorVertex f) (functorVertex g)
    rw [hf, hg]
    exact h'
  have k := parametrizedFiberTransport_at_edgeIso p (intervalMappingEdgeOfVertex (a.app _ v))
  have he : intervalMappingVertexOfEdge (intervalMappingEdgeOfVertex (a.app _ v)) = a.app _ v :=
    (intervalMappingEdgeVertexEquiv x y).apply_symm_apply _
  rw [he] at k
  exact hi ≪≫ k

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
