module

public import SerrePositivity.InfinityCategories.F2.Ind.IndConeEndpointFaceComparison
public import SerrePositivity.InfinityCategories.F2.Ind.IndConeEndpointEvaluationPrism

/-!
概要：再構成した終点族を元の極大点評価と同定し、元の実終点族との比較を渡す。
方針：元の C 全図式と全余錐の等号を、同じ実引き戻しで照合する。
規約：元の指定点と全族を取り替えず、同じ比較同型を保持する。
使われ方：極大点での指定評価下の余錐と共終性への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {κ : Cardinal.{u}} {L C : SSet.{u}} [Quasicategory C]
  {D : (SSet.uliftFunctor.{u + 1, u}).obj (join L (Δ[0] : SSet.{u})) ⟶ IndInfinity κ C}
  {T : SSet.{u + 1}} {q : T ⟶ diagramComma κ D}
  {G : JoinCocone (q ≫ diagramCommaRestriction κ D (joinInl L (Δ[0] : SSet.{u})))}
  (V : IndConeExtendedSliceData κ D q G)
/-- 概要：標準終点 comma に表示を戻しても、同じ元の全底余錐を厳密に回収する。
方針：元の点の等号による引き戻し移送。規約：全射の等号。使われ方：元の評価との同定。 -/
lemma indConeEndpointReconstructedFace_uncurry :
    sliceOverUncurry (indConeEndpointReconstructedRawFace V ≫
      (indConeEndpointCommaIso κ D).hom ≫
      pullback.snd (indYoneda κ C) (sliceOverProjection (SSet.yonedaEquiv.symm
        (D.app (Opposite.op ⦋0⦌) (ULift.up (coneApex L)))))) = indConeEndpointBaseCone V := by
  have h := coneCommaTransport_uncurry (indYoneda κ C) (indConeEndpoint_point κ D)
    (indConeEndpointReconstructedRawFace V)
  rw [indConeEndpointReconstructedRawFace_slice, sliceOverUncurry_curry] at h
  convert h using 1 <;> rfl
/-- 概要：再構成した終点族は元の同じ極大点評価そのもの。
方針：元の C 全図式と全余錐を同時に照合。規約：同型でなく全射の等号。
使われ方：終点族の比較を元の指定評価下の余錐へ移す。 -/
lemma indConeEndpointEvaluation_eq_reconstructed :
    indConeExtendedCommaFamily V ≫ diagramCommaEvaluation κ D (coneApex L) =
      indConeEndpointReconstructedRawFace V ≫ (indConeEndpointCommaIso κ D).hom := by
  apply pullback.hom_ext
  · simpa only [Category.assoc, indConeEndpointCommaIso_projection,
      indConeEndpointReconstructedRawFace_projection] using indConeEndpointEvaluation_projection V
  · apply sliceOverUncurry_injective
    simp only [Category.assoc]
    rw [indConeEndpointEvaluation_uncurry, indConeEndpointReconstructedFace_uncurry]
/-- 概要：元の実終点族を、元の同じ極大点評価の全族へ比較する指定同型。
方針：元の slice 比較と元の評価の厳密な回収。規約：同じ両全族を保持。
使われ方：新しい極大点での指定変換下の余錐と共終性。 -/
def indConeEndpointEvaluationIso :
    FunctorIso (indConeEndpointRawFace V ≫ (indConeEndpointCommaIso κ D).hom)
      (indConeExtendedCommaFamily V ≫ diagramCommaEvaluation κ D (coneApex L)) := by
  rw [indConeEndpointEvaluation_eq_reconstructed]
  exact indConeEndpointFaceIso V
end SerrePositivity.InfinityCategories.F2.Ind
