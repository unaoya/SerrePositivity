module

public import SerrePositivity.InfinityCategories.F2.Ind.IndConeEndpointSliceNaturality
public import SerrePositivity.InfinityCategories.F2.Ind.IndConeEndpointReconstructedFace

/-!
概要：元の実終点族と再構成終点族の旧族制限は、初期全円柱で厳密に決まる。
方針：元の全終点境界と全底余錐を、同じ終点面で回収する。
規約：元の C 全係数と全変換の等号を保持する。
使われ方：再構成を選び直した二つの指定比較の元の両端を照合する。
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
/-- 概要：実終点族の旧族制限は、元の初期終点族の同じ終点面。
方針：元の全終点族の旧族境界を制限。規約：全射の等号。使われ方：比較の端点の回収。 -/
lemma indConeEndpointRawFace_old :
    joinInl T (Δ[0] : SSet.{u + 1}) ≫ indConeEndpointRawFace V =
    tensorRightPoint T (joinInr ((SSet.uliftFunctor.{u + 1, u}).obj L) Δ[0]) ≫
      indConeEndpointRaw V.initial := by
  rw [indConeEndpointRawFace, ← Category.assoc, tensorRightPoint_naturality,
    Category.assoc, V.endpoint_old]
/-- 概要：同じ元の初期全円柱から得られる実終点族の旧族制限は変わらない。
方針：元の全境界の等号を回収。規約：全射の等号。使われ方：指定比較の端点の照合。 -/
lemma indConeEndpointRawFace_old_eq (V' : IndConeExtendedSliceData κ D q G)
    (hInitial : V.initial = V'.initial) :
    joinInl T (Δ[0] : SSet.{u + 1}) ≫ indConeEndpointRawFace V =
      joinInl T (Δ[0] : SSet.{u + 1}) ≫ indConeEndpointRawFace V' := by
  rw [indConeEndpointRawFace_old, indConeEndpointRawFace_old, hInitial]
/-- 概要：同じ初期全円柱を保持する再構成では、実再構成終点族の旧族制限も変わらない。
方針：同じ C 全族と元の全底余錐を厳密に回収。規約：全射の等号。使われ方：相対反映。 -/
lemma indConeEndpointReconstructedRawFace_old_eq (V' : IndConeExtendedSliceData κ D q G)
    (hInitial : V.initial = V'.initial) :
    joinInl T (Δ[0] : SSet.{u + 1}) ≫ indConeEndpointReconstructedRawFace V =
      joinInl T (Δ[0] : SSet.{u + 1}) ≫ indConeEndpointReconstructedRawFace V' := by
  apply pullback.hom_ext
  · simp only [Category.assoc, indConeEndpointReconstructedRawFace_projection]
    simpa only [Category.assoc] using congrArg (fun f ↦ f ≫
      pullback.fst (indYoneda κ C) (sliceOverProjection (indConeEndpointPoint κ D)))
      (indConeEndpointRawFace_old_eq V V' hInitial)
  · apply sliceOverUncurry_injective (indConeEndpointPoint κ D)
    simp only [Category.assoc, indConeEndpointReconstructedRawFace_slice]
    rw [sliceOverUncurry_precomp, sliceOverUncurry_curry,
      sliceOverUncurry_precomp, sliceOverUncurry_curry]
    rw [indConeEndpointBaseCone_old, indConeEndpointBaseCone_old, hInitial]
end SerrePositivity.InfinityCategories.F2.Ind
