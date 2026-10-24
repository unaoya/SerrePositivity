module

public import SerrePositivity.InfinityCategories.F2.Ind.IndConeEndpointSliceConeTip
public import SerrePositivity.InfinityCategories.F2.Ind.IndConeExtendedCommaFamily
public import SerrePositivity.InfinityCategories.F2.Ind.IndConeShapePoint
public import SerrePositivity.InfinityCategories.F2.Ind.DiagramRightFamilyPoint

/-!
概要：元の極大点評価の C 全図式と全余錐を、再構成した同じ終点面へ厳密に戻す。
方針：元の全円柱と C 全族の点制限を、同じ余錐点の宇宙比較で照合する。
規約：元の C 全係数と指定極大点の全変換を保持する。
使われ方：再構成した終点族と元の極大点評価の厳密な同定。
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
/-- 概要：元の極大点評価の全余錐は、再構成した終点面の同じ全底余錐。
方針：元の全円柱の点制限と余錐点の厳密な宇宙比較。規約：全射の等号。
使われ方：再構成した終点族を元の指定評価そのものと同定する。 -/
lemma indConeEndpointEvaluation_uncurry :
    sliceOverUncurry (indConeExtendedCommaFamily V ≫
      diagramCommaEvaluation κ D (coneApex L) ≫
      pullback.snd (indYoneda κ C) (sliceOverProjection (SSet.yonedaEquiv.symm
        (D.app (Opposite.op ⦋0⦌) (ULift.up (coneApex L)))))) = indConeEndpointBaseCone V := by
  rw [diagramCommaRightPrism_point, indConeExtendedCommaFamily_prism,
    indConeExtendedPrism, ← Category.assoc, tensorRightPoint_whiskerLeft,
    indConeShape_point]
  simp only [indConeEndpointBaseCone, indConeEndpointSliceCone, Category.assoc]
/-- 概要：元の極大点評価の C 全図式は、同じ元の終点族の C 全図式そのもの。
方針：元の C 全族の点制限と同じ宇宙比較。規約：全係数の等号。
使われ方：同じ実 comma で元の指定評価の全族を厳密に回収する。 -/
lemma indConeEndpointEvaluation_projection :
    indConeExtendedCommaFamily V ≫ diagramCommaEvaluation κ D (coneApex L) ≫
      leftKanProjection (indYoneda κ C)
        (D.app (Opposite.op ⦋0⦌) (ULift.up (coneApex L))) =
    indConeEndpointRawFace V ≫
      pullback.fst (indYoneda κ C) (sliceOverProjection (indConeEndpointPoint κ D)) := by
  rw [diagramCommaOriginalFamily_point, indConeExtendedCommaFamily_originalFamily,
    indConeExtendedFamily, ← Category.assoc, tensorRightPoint_whiskerLeft,
    indConeShape_point]
  simp only [indConeEndpointRawFace, Category.assoc]
end SerrePositivity.InfinityCategories.F2.Ind
