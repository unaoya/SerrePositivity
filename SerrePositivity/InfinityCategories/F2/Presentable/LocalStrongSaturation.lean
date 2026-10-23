module

public import SerrePositivity.InfinityCategories.F2.Presentable.LocalArrowColimits
public import SerrePositivity.InfinityCategories.F2.Presentable.LocalPushoutEquivalences

/-!
概要：元の辺集合上で局所同値の強飽和性を、小さい添字の宇宙を明示して証明する。
方針：元の余錐の評価・prism・全 Hom の普遍性を、厳密な射と同型で照合する。
規約：F2 は読み取り専用。使われ方：HTT 5.5.4.5・5.5.4.11 の強飽和性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 小さい添字の宇宙を明示した、元の辺集合の強飽和性の条件。 -/
def IsStronglySaturatedEdgeSetOfShapes {X : SSet.{v}} [Quasicategory X]
    (smallShape : SSet.{u} → SSet.{v}) (S : Set (X _⦋1⦌)) : Prop :=
  (∀ {x y : X _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj X) x y),
    IsInvertibleEdge e → e.edge ∈ S) ∧
  (∀ (R : (Δ[1] : SSet.{v}) ⊗ Δ[1] ⟶ X), IsPushoutSquare R →
    SSet.yonedaEquiv (squareBottomEdge ≫ R) ∈ S → SSet.yonedaEquiv (squareTopEdge ≫ R) ∈ S) ∧
  (∀ (K : SSet.{u})
    (r : smallShape K ⟶ (ihom (Δ[1] : SSet.{v})).obj X)
    (c : JoinCocone r), IsColimitCone c →
    (∀ k : (smallShape K) _⦋0⦌,
      arrowVertexEdge (r.app (Opposite.op ⦋0⦌) k) ∈ S) →
    arrowVertexEdge c.vertex ∈ S) ∧
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
lemma localEquivalences_stronglySaturated {X : SSet.{max u v}} [Quasicategory X]
    (W : Set (X _⦋1⦌))
    (hX : ∀ (K : SSet.{u}) (p : (SSet.uliftFunctor.{v, u}).obj K ⟶ X), HasColimit p) :
    IsStronglySaturatedEdgeSetOfShapes (SSet.uliftFunctor.{v, u}).obj (localEquivalences W) := by
  refine ⟨localEquivalences_mem_of_isInvertibleEdge W,
    localEquivalences_pushout_bottom_top W, ?_, ?_, ?_, ?_⟩
  · intro K _r c hc
    exact localEquivalences_arrowColimit W (hX K) c hc
  · intro x y z e01 e12 e02 t
    exact localEquivalences_compStruct W t
  · intro x y z e01 e12 e02 t
    exact localEquivalences_compStruct_cancel_left W t
  · intro x y z e01 e12 e02 t
    exact localEquivalences_compStruct_cancel_right W t

end SerrePositivity.InfinityCategories.HomotopyLimits
