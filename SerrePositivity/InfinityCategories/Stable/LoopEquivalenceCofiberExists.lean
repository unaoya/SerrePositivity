module
public import SerrePositivity.InfinityCategories.Stable.LoopEquivalenceCofiberRotation
public import SerrePositivity.InfinityCategories.Stable.LoopEquivalenceExcision
public import SerrePositivity.InfinityCategories.Stable.SquareTranspose

/-!
概要：有限極限と実 loop 同値から、全ての辺の実 cofiber を構成する。
方針：元の辺の fiber を切除で cofiber にし、その列を一回回転する。
規約：有限余極限や安定性を追加仮定にしない。
使われ方：一般安定性判定の全 cofiber の存在条件。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：指定した元の辺を底辺として持つ cofiber 四角形が存在する。
方針：同じ辺を右辺に持つ fiber 四角形を切除し、零終点を付加して回転する。
規約：指定辺との一致はホモトピー圏でなく実辺の等式。
使われ方：IsStable の cofiber_exists フィールド。 -/
lemma cofiberSquare_nonempty_of_loopEquivalence {X : SSet.{u}}
    [Quasicategory X] [HasZeroVertex X] [HasFiniteLimits X]
    (s : X ⟶ loopDiagrams X) (hs : s ≫ loopDiagramEvaluation X 1 1 = 𝟙 X)
    (hΩ : IsQCatEquivalence (s ≫ loopDiagramEvaluation X 0 0))
    {x y : X _⦋0⦌} (f : Truncated.Edge (X := (truncation 2).obj X) x y) :
    Nonempty (CofiberSquare f) := by
  obtain ⟨t⟩ := exists_fiberSquare_of_cospan_limits
    (fun p ↦ HasFiniteLimits.hasLimit p) f
  have ht := isPushoutSquare_of_isPullback_of_loopEquivalence s hs hΩ t.square t.isPullback
  obtain ⟨r⟩ := nonempty_cofiberRotationRectangle_of_loopEquivalence
    s hs hΩ t.toZeroTriangle ht
  refine ⟨{
    square := r.rotatedZeroTriangle.square
    zero_corner := r.rotatedZeroTriangle.zero_corner
    isPushout := r.rotated_isCofiber
    bottom_edge := ?_ }⟩
  change squareBottomEdge ≫ ((β_ Δ[1] Δ[1]).hom ≫ pastingSquare r.diagram 0) = _
  rw [← Category.assoc, squareBottomEdge_transpose]
  rw [← pastingSquare_sharedEdge, r.left_eq]
  exact t.right_edge

end SerrePositivity.InfinityCategories
