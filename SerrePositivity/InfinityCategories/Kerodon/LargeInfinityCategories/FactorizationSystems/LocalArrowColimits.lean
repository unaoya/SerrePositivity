module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Cocone
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePath
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.FunctorLimits
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.PrismContraction
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeCoconeAbsolute
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CoconeValEquality
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.LocalEquivalences
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.ArrowCoconePrism
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitPrismLocalApex
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitPrismTotalCocone
public import SerrePositivity.InfinityCategories.HTT.Section5_1_2.FunctorColimitEvaluation
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.PrismVertexEvaluation

/-!
概要：元の矢印圏内の任意の指定余極限余錐について、局所同値な辺集合の閉性を証明する。
方針：元の余錐の評価・prism・全 Hom の普遍性を、厳密な射と同型で照合する。
規約：F2 は読み取り専用。使われ方：HTT 5.5.4.5・5.5.4.11 の強飽和性。

対応節は Kerodon 9.6（Tag 04KF）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FactorizationSystems

/-- 両端評価が余極限なら、局所同値な図式の元の矢印圏の余錐の頂点辺も局所同値。 -/
lemma localEquivalences_arrowCocone_of_endpoints {K X : SSet.{u}} [Quasicategory X]
    (W : Set (X _⦋1⦌)) {r : K ⟶ (ihom (Δ[1] : SSet.{u})).obj X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone r)
    (h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanPostcomposeCocone
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 0)) c))
    (h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanPostcomposeCocone
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 1)) c))
    (h : ∀ k : K _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.arrowVertexEdge (r.app (Opposite.op ⦋0⦌) k) ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.localEquivalences W) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.arrowVertexEdge c.vertex ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.localEquivalences W := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.arrowCocone_vertex_prismEdge]
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.localEquivalences_colimitPrism_apex W (uncurry c.val)
  · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isColimitCone_iff_of_cocone_val_eq _ _ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.arrowCocone_endpoint_val c 0)).mpr h₀
  · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isColimitCone_iff_of_cocone_val_eq _ _ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.arrowCocone_endpoint_val c 1)).mpr h₁
  · intro k
    rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.arrowCocone_prism_diagram, ← _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.uncurry_vertex_prismEvaluation]
    exact h k

/-- 指定形状の余極限の存在の下、局所同値な図式の元の任意の矢印圏の余極限も局所同値。 -/
lemma localEquivalences_arrowColimit {K X : SSet.{u}} [Quasicategory X]
    (W : Set (X _⦋1⦌)) (hX : ∀ p : K ⟶ X, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit p)
    {r : K ⟶ (ihom (Δ[1] : SSet.{u})).obj X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone r) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
    (h : ∀ k : K _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.arrowVertexEdge (r.app (Opposite.op ⦋0⦌) k) ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.localEquivalences W) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.arrowVertexEdge c.vertex ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.localEquivalences W := by
  apply localEquivalences_arrowCocone_of_endpoints W c
  · exact _root_.SerrePositivity.InfinityCategories.HTT.Section5_1_2.isColimitCone_functor_evaluation_of_pointwise_exists c hc
      (fun k ↦ hX (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.evaluateFunctorDiagram r k)) _
  · exact _root_.SerrePositivity.InfinityCategories.HTT.Section5_1_2.isColimitCone_functor_evaluation_of_pointwise_exists c hc
      (fun k ↦ hX (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.evaluateFunctorDiagram r k)) _
  · exact h

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FactorizationSystems
