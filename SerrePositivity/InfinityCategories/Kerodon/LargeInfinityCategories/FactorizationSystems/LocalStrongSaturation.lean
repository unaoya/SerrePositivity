module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Cocone
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.Pullback
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PushoutShape
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FactorizationSystems.LocalArrowColimits
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.LocalEquivalenceTriangles
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.LocalEquivalences
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.LocalPushoutEquivalences
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ArrowCoconePrism
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：元の辺集合上で局所同値の強飽和性を、小さい添字の宇宙を明示して証明する。
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

/-- 小さい添字の宇宙を明示した、元の辺集合の強飽和性の条件。 -/
@[kerodon 06XK]
def IsStronglySaturatedEdgeSetOfShapes {X : SSet.{v}} [Quasicategory X]
    (smallShape : SSet.{u} → SSet.{v}) (S : Set (X _⦋1⦌)) : Prop :=
  (∀ {x y : X _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj X) x y),
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e → e.edge ∈ S) ∧
  (∀ (R : (Δ[1] : SSet.{v}) ⊗ Δ[1] ⟶ X), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare R →
    SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ R) ∈ S → SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ R) ∈ S) ∧
  (∀ (K : SSet.{u})
    (r : smallShape K ⟶ (ihom (Δ[1] : SSet.{v})).obj X)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone r), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c →
    (∀ k : (smallShape K) _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.arrowVertexEdge (r.app (Opposite.op ⦋0⦌) k) ∈ S) →
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.arrowVertexEdge c.vertex ∈ S) ∧
  (∀ {x y z : X _⦋0⦌}
    {e01 : SSet.Truncated.Edge (X := (truncation 2).obj X) x y}
    {e12 : SSet.Truncated.Edge (X := (truncation 2).obj X) y z}
    {e02 : SSet.Truncated.Edge (X := (truncation 2).obj X) x z},
    SSet.Truncated.Edge.CompStruct e01 e12 e02 → e01.edge ∈ S → e12.edge ∈ S → e02.edge ∈ S) ∧
  (∀ {x y z : X _⦋0⦌}
    {e01 : SSet.Truncated.Edge (X := (truncation 2).obj X) x y}
    {e12 : SSet.Truncated.Edge (X := (truncation 2).obj X) y z}
    {e02 : SSet.Truncated.Edge (X := (truncation 2).obj X) x z},
    SSet.Truncated.Edge.CompStruct e01 e12 e02 → e01.edge ∈ S → e02.edge ∈ S → e12.edge ∈ S) ∧
  (∀ {x y z : X _⦋0⦌}
    {e01 : SSet.Truncated.Edge (X := (truncation 2).obj X) x y}
    {e12 : SSet.Truncated.Edge (X := (truncation 2).obj X) y z}
    {e02 : SSet.Truncated.Edge (X := (truncation 2).obj X) x z},
    SSet.Truncated.Edge.CompStruct e01 e12 e02 → e12.edge ∈ S → e02.edge ∈ S → e01.edge ∈ S)

/-- 小さい形状の余極限を持つ対象圏で、指定辺への局所同値の元の辺集合は強飽和。 -/
@[kerodon 06XK]
lemma localEquivalences_stronglySaturated {X : SSet.{max u v}} [Quasicategory X]
    (W : Set (X _⦋1⦌))
    (hX : ∀ (K : SSet.{u}) (p : (SSet.uliftFunctor.{v, u}).obj K ⟶ X), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit p) :
    IsStronglySaturatedEdgeSetOfShapes (SSet.uliftFunctor.{v, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.localEquivalences W) := by
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.localEquivalences_mem_of_isInvertibleEdge W,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.localEquivalences_pushout_bottom_top W, ?_, ?_, ?_, ?_⟩
  · intro K _r c hc
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FactorizationSystems.localEquivalences_arrowColimit W (hX K) c hc
  · intro x y z e01 e12 e02 t
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.localEquivalences_compStruct W t
  · intro x y z e01 e12 e02 t
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.localEquivalences_compStruct_cancel_left W t
  · intro x y z e01 e12 e02 t
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.localEquivalences_compStruct_cancel_right W t

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FactorizationSystems
