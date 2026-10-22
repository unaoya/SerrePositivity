module

public import SerrePositivity.InfinityCategories.F2.Ind.TerminalCarrierConeConditions
public import SerrePositivity.InfinityCategories.F2.Ind.TerminalCarrierLift

/-!
概要：共通部分複体内の同じ余錐を、元の実現図式の余錐へ持ち上げる。
方針：全単体の所属と頂点の一致を確認した元の二成分を同時に持ち上げる。
規約：左因子への制限、値写像、添字写像の三つの等式を厳密に保つ。
使われ方：cofinal 性の coslice 引き戻しの有限余錐。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {I : Type u} [Preorder I] {X K : SSet.{u}}

/-- 同じ終頂点への余錐の元の二成分は、元の図式を厳密に延長する持ち上げを持つ。 -/
lemma exists_terminalCarrier_cone_lift (A : I → X.Subcomplex) (z : I → X _⦋0⦌)
    (a : K ⟶ (terminalCarrier A z).toSSet)
    (F : join K (Δ[0] : SSet.{u}) ⟶ X) (q : join K (Δ[0] : SSet.{u}) ⟶ nerve I) (i : I)
    (hF : joinInl K Δ[0] ≫ F = a ≫ terminalCarrierValue A z)
    (hq : joinInl K Δ[0] ≫ q = a ≫ terminalCarrierProjection A z)
    (hbound : Subcomplex.range F ≤ A i)
    (hFapex : F.app _ (coneApex K) = z i) (hqapex : q.app _ (coneApex K) = nerveVertex i) :
    ∃ G : join K (Δ[0] : SSet.{u}) ⟶ (terminalCarrier A z).toSSet,
      joinInl K Δ[0] ≫ G = a ∧ G ≫ terminalCarrierValue A z = F ∧
        G ≫ terminalCarrierProjection A z = q := by
  obtain ⟨hmem, hv⟩ := terminalCarrierCone_conditions A z a F q i hF hq hbound hFapex hqapex
  let G := terminalCarrierLift A z F q hmem hv
  have hval : G ≫ terminalCarrierValue A z = F := terminalCarrierLift_value _ _ _ _ _ _
  have hproj : G ≫ terminalCarrierProjection A z = q := terminalCarrierLift_projection _ _ _ _ _ _
  refine ⟨G, ?_, hval, hproj⟩
  apply terminalCarrier_hom_ext A z
  · rw [Category.assoc, hval]
    exact hF
  · rw [Category.assoc, hproj]
    exact hq

end SerrePositivity.InfinityCategories.F2.Ind
