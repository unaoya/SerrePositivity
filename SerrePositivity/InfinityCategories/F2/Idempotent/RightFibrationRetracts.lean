module

public import SerrePositivity.InfinityCategories.F2.Idempotent.WeakPointLifting
public import SerrePositivity.InfinityCategories.F2.Idempotent.WeakEndpoints
public import SerrePositivity.InfinityCategories.F2.Idempotent.WeakExtension

/-!
概要：右 fibration により、指定した元の頂点の底の retract を全体へ持ち上げる。
方針：元の分裂三角形を元の弱い全図式へ降ろし、分裂点を固定して持ち上げる。
規約：元の頂点を保持し、持ち上げた非分裂点の像は指定した底の点そのもの。
使われ方：HTT 5.1.4.4 の slice の冪等完備化の対象条件。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 指定した元の分裂点を持つ底の retract は、右 fibration の全体へ持ち上がる。 -/
lemma rightFibration_retract_lift {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    (p : X ⟶ Y) [RightFibration p] (x : X _⦋0⦌) (y : Y _⦋0⦌)
    (r : VertexRetraction (p.app (Opposite.op ⦋0⦌) x) y) :
    ∃ z : X _⦋0⦌, p.app (Opposite.op ⦋0⦌) z = y ∧ IsVertexRetractOf x z := by
  obtain ⟨t, _hi, _hr⟩ := r.triangle_exists
  have h : SSet.yonedaEquiv.symm x ≫ p = weakImagePoint ≫ t.weakDiagram := by
    rw [t.weakDiagram_imagePoint, ← SSet.yonedaEquiv_symm_comp]
  obtain ⟨e, he, hep⟩ := weakDiagram_lift_exists p t.weakDiagram
    (SSet.yonedaEquiv.symm x) h
  obtain ⟨F, hF⟩ := weakDiagram_extension_exists e
  let s : StrongSplitting (idemInclusion ≫ F) := ⟨F, rfl⟩
  have hx : s.vertex = x := by
    change F.app (Opposite.op ⦋0⦌) (nerveEquiv.symm walkingImage) = x
    rw [← hF, ← Category.assoc, weakComparison_imagePoint] at he
    have hh := congrArg SSet.yonedaEquiv he
    simpa only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] using hh
  let z := F.app (Opposite.op ⦋0⦌) (nerveEquiv.symm walkingSource)
  have hy : p.app (Opposite.op ⦋0⦌) z = y := by
    have ht := t.weakDiagram_sourcePoint
    rw [← hep, ← hF] at ht
    simp only [← Category.assoc] at ht
    rw [weakComparison_sourcePoint] at ht
    have hh := congrArg SSet.yonedaEquiv ht
    simpa only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] using hh
  refine ⟨z, hy, ?_⟩
  have hs : IsVertexRetractOf s.vertex z := ⟨s.vertexRetraction⟩
  exact hx ▸ hs

end SerrePositivity.InfinityCategories.F2.Idempotent
