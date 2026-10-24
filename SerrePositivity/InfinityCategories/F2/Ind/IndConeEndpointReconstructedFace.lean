module

public import SerrePositivity.InfinityCategories.F2.Ind.IndConeEndpointSliceConeTip

/-!
概要：元の C 全族と再構成された終点面を、元の同じ実終点 comma へ戻す。
方針：同じ全底余錐を slice へ curry し、元の C 全族と厳密に引き戻す。
規約：元の C 全係数と同じ底余錐を保持する。
使われ方：元の実終点族と元の極大点評価の比較。
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
/-- 概要：元の C 全族と再構成された終点面の全余錐を、同じ実終点 comma へ戻す。
方針：同じ元の二射を厳密に引き戻す。規約：全係数を保持。使われ方：極大点の評価比較。 -/
def indConeEndpointReconstructedRawFace : join T (Δ[0] : SSet.{u + 1}) ⟶
    pullback (indYoneda κ C) (sliceOverProjection (indConeEndpointPoint κ D)) :=
  pullback.lift
    (indConeEndpointRawFace V ≫
      pullback.fst (indYoneda κ C) (sliceOverProjection (indConeEndpointPoint κ D)))
    (sliceOverCurry (indConeEndpointBaseCone V) (indConeEndpointBaseCone_tip V)) (by
      rw [sliceOverCurry_projection]
      exact (indConeEndpointBaseCone_source V).symm)
/-- 概要：再構成した実終点族は元の同じ C 全族を厳密に保持する。
方針：元の第一射影。規約：全係数の等号。使われ方：元の終点族との比較。 -/
lemma indConeEndpointReconstructedRawFace_projection :
    indConeEndpointReconstructedRawFace V ≫
      pullback.fst (indYoneda κ C) (sliceOverProjection (indConeEndpointPoint κ D)) =
    indConeEndpointRawFace V ≫
      pullback.fst (indYoneda κ C) (sliceOverProjection (indConeEndpointPoint κ D)) :=
  pullback.lift_fst _ _ _
/-- 概要：再構成した実終点族は元の同じ底余錐の slice 表示を厳密に回収する。
方針：元の第二射影。規約：全射の等号。使われ方：元の全終点変換との比較。 -/
lemma indConeEndpointReconstructedRawFace_slice :
    indConeEndpointReconstructedRawFace V ≫
      pullback.snd (indYoneda κ C) (sliceOverProjection (indConeEndpointPoint κ D)) =
    sliceOverCurry (indConeEndpointBaseCone V) (indConeEndpointBaseCone_tip V) :=
  pullback.lift_snd _ _ _
end SerrePositivity.InfinityCategories.F2.Ind
