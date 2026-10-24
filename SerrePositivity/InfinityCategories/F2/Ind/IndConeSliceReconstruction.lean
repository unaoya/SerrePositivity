module

public import SerrePositivity.InfinityCategories.F2.Ind.IndConeEndpointRawExtension
public import SerrePositivity.InfinityCategories.F2.Ind.ConeTensorThreeBoundaryExtension
public import SerrePositivity.InfinityCategories.F2.Ind.ConeSlicePrismApex

/-!
概要：実終点 comma の全拡張から、元の旧族全体を固定する実 slice 円柱を再構成する。
方針：終点族の slice 成分と指定下方全余錐を貼り、同じ終対象へ相対延長する。
規約：元の旧族の全円柱・下方全余錐・補間族を全射の等号で保持する。
使われ方：有限半順序図式の点追加で同じ元の diagram comma の実余錐へ戻す。
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
/-- 概要：終点族の実全拡張は、元の旧族と下方全余錐を固定する円柱へ戻る。
方針：同じ slice の三境界相対再構成。規約：全射の等号。使われ方：元の実余錐。 -/
lemma exists_indConeSlice_reconstruction (V : IndConeSliceInterpolationData κ D q G)
    (E : join T (Δ[0] : SSet.{u + 1}) ⊗
      join ((SSet.uliftFunctor.{u + 1, u}).obj L) Δ[0] ⟶
        pullback (indYoneda κ C) (sliceOverProjection (indConeEndpointPoint κ D)))
    (hF : (joinInl T (Δ[0] : SSet.{u + 1}) ▷
      join ((SSet.uliftFunctor.{u + 1, u}).obj L) Δ[0]) ≫ E = indConeEndpointRaw V)
    (hG : (join T (Δ[0] : SSet.{u + 1}) ◁
      joinInl ((SSet.uliftFunctor.{u + 1, u}).obj L) Δ[0]) ≫ E =
        indConeLowerEndpointRaw V) :
    ∃ R : join (join T (Δ[0] : SSet.{u + 1})) Δ[0] ⊗
      join ((SSet.uliftFunctor.{u + 1, u}).obj L) Δ[0] ⟶
        sliceOver (indConeEndpointPoint κ D),
      (joinInl (join T (Δ[0] : SSet.{u + 1})) Δ[0] ▷
        join ((SSet.uliftFunctor.{u + 1, u}).obj L) Δ[0]) ≫ R =
          E ≫ pullback.snd (indYoneda κ C) (sliceOverProjection (indConeEndpointPoint κ D)) ∧
      (join (join T (Δ[0] : SSet.{u + 1})) Δ[0] ◁
        joinInl ((SSet.uliftFunctor.{u + 1, u}).obj L) Δ[0]) ≫ R = V.lower ∧
      (joinMap (joinInl T (Δ[0] : SSet.{u + 1})) (𝟙 Δ[0]) ▷
        join ((SSet.uliftFunctor.{u + 1, u}).obj L) Δ[0]) ≫ R = V.prism := by
  have h : (join T (Δ[0] : SSet.{u + 1}) ◁
      joinInl ((SSet.uliftFunctor.{u + 1, u}).obj L) Δ[0]) ≫
      (E ≫ pullback.snd _ _) =
    (joinInl (join T (Δ[0] : SSet.{u + 1})) Δ[0] ▷
      (SSet.uliftFunctor.{u + 1, u}).obj L) ≫ V.lower := by
    rw [← Category.assoc, hG, indConeLowerEndpointRaw_slice]
  have hf : (joinInl T (Δ[0] : SSet.{u + 1}) ▷
      join ((SSet.uliftFunctor.{u + 1, u}).obj L) Δ[0]) ≫
      (E ≫ pullback.snd _ _) =
    (joinInl T (Δ[0] : SSet.{u + 1}) ▷
      join ((SSet.uliftFunctor.{u + 1, u}).obj L) Δ[0]) ≫ V.prism := by
    rw [← Category.assoc, hF, indConeEndpointRaw_slice]
  exact exists_coneTensor_threeBoundary_extension (joinInl T (Δ[0] : SSet.{u + 1}))
    (E ≫ pullback.snd _ _) V.lower V.prism h hf V.lower_boundary.symm
    (coneSlicePrism_apex_isTerminal (indConeNormalizedDiagram κ D) V.prism V.tip)
end SerrePositivity.InfinityCategories.F2.Ind
