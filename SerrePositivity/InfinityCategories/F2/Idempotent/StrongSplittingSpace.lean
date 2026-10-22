module

public import SerrePositivity.InfinityCategories.F2.Idempotent.SplittingRestriction

/-!
概要：指定した元の全 Idem 図式上の全強分裂空間を、元の制限の fiber として構成する。
方針：全次数で同じ元の全図式を固定し、零単体は元の厳密な強い分裂と全単射にする。
規約：弱い retract の三角形上の fiber ではなく、元の全 Idem 図式を固定する。
使われ方：HTT 4.4.5.16 の全強分裂空間の可縮性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 元の全 Idem 図式を全次数で固定した、元の全強分裂図式の空間。 -/
def strongSplittingSpace {X : SSet.{u}} (d : CoherentIdempotent X) : SSet.{u} :=
  vertexFiber (strongSplittingRestriction X) (functorVertex d)

/-- 元の厳密な強い分裂は、同じ全図式上の全分裂空間の頂点を与える。 -/
def strongSplittingSpaceVertex {X : SSet.{u}} {d : CoherentIdempotent X}
    (s : StrongSplitting d) : (strongSplittingSpace d) _⦋0⦌ :=
  ⟨functorVertex s.val, by
    rw [pinchedConstant_zero]
    change functorVertex (idemInclusion ≫ s.val) = functorVertex d
    rw [s.property]⟩

/-- 元の全分裂空間の頂点から、同じ元の全図式の厳密な強い分裂を回収する。 -/
def strongSplittingOfSpaceVertex {X : SSet.{u}} {d : CoherentIdempotent X}
    (x : (strongSplittingSpace d) _⦋0⦌) : StrongSplitting d := by
  let F := (functorVertexEquiv SplitShape X).symm x.val
  have hf : functorVertex F = x.val := (functorVertexEquiv SplitShape X).apply_symm_apply _
  refine ⟨F, ?_⟩
  apply (functorVertexEquiv IdemShape X).injective
  have h : (strongSplittingRestriction X).app (Opposite.op ⦋0⦌) x.val = functorVertex d :=
    x.property.trans (pinchedConstant_zero _)
  exact (congrArg (fun v ↦ (strongSplittingRestriction X).app (Opposite.op ⦋0⦌) v) hf).trans h

/-- 元の全分裂空間の零単体は、元の厳密な強い分裂そのものと全単射。 -/
def strongSplittingSpaceVertexEquiv {X : SSet.{u}} (d : CoherentIdempotent X) :
    StrongSplitting d ≃ (strongSplittingSpace d) _⦋0⦌ where
  toFun := strongSplittingSpaceVertex
  invFun := strongSplittingOfSpaceVertex
  left_inv s := Subtype.ext ((functorVertexEquiv SplitShape X).symm_apply_apply s.val)
  right_inv x := Subtype.ext ((functorVertexEquiv SplitShape X).apply_symm_apply x.val)

end SerrePositivity.InfinityCategories.F2.Idempotent
