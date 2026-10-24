module

public import SerrePositivity.InfinityCategories.F2.Ind.IndConeEndpointSliceCone
public import SerrePositivity.InfinityCategories.F2.Ind.PointSliceIdentityProjection

/-!
概要：再構成した終点面は、元の点の同じ恒等頂点で終わる。
方針：元の D 側面を制限し、同じ標準 slice 切断の恒等終点を回収する。
規約：元の全底余錐と全始域境界を厳密に保持する。
使われ方：同じ底と恒等終点を固定した終点面の相対比較。
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
/-- 概要：再構成した終点面の終端は元の点の同じ恒等頂点の全写像。
方針：同じ D 側面の終点を制限。規約：全射の等号。使われ方：元の底を固定する比較。 -/
lemma indConeEndpointSliceCone_tip :
    joinInr (join T (Δ[0] : SSet.{u + 1})) Δ[0] ≫ indConeEndpointSliceCone V =
    SSet.yonedaEquiv.symm (pointSliceIdentity (indConeEndpointPoint κ D)) := by
  rw [indConeEndpointSliceCone, ← Category.assoc, tensorRightPoint_naturality,
    Category.assoc, indConeExtendedSlice_tip, ← Category.assoc, tensorRightPoint_snd,
    SSet.const_comp, SSet.yonedaEquiv_symm_zero]
  congr 1
  have h := coneTerminalSliceSection_tip (indConeNormalizedDiagram κ D)
  simp only [SSet.yonedaEquiv_comp] at h
  convert h using 1 <;> rfl
/-- 概要：同じ終点面の終端の全錐は元の点の恒等錐そのもの。
方針：同じ恒等頂点を uncurry。規約：全射の等号。使われ方：相対比較の恒等終点条件。 -/
lemma indConeEndpointSliceCone_tip_uncurry :
    sliceOverUncurry (joinInr (join T (Δ[0] : SSet.{u + 1})) Δ[0] ≫
      indConeEndpointSliceCone V) = SSet.const (SSet.yonedaEquiv (indConeEndpointPoint κ D)) := by
  rw [indConeEndpointSliceCone_tip, sliceOverUncurry_yoneda]
  rfl
/-- 概要：再構成した終点面の元の底余錐の終点は、元の同じ指定点写像。
方針：元の恒等頂点を射影。規約：全射の等号。使われ方：同じ底と終点を固定する比較。 -/
lemma indConeEndpointBaseCone_tip :
    joinInr (join T (Δ[0] : SSet.{u + 1})) Δ[0] ≫ indConeEndpointBaseCone V =
      indConeEndpointPoint κ D := by
  rw [indConeEndpointBaseCone, ← Category.assoc, indConeEndpointSliceCone_tip,
    pointSliceIdentity_point_projection]
/-- 概要：元の終点族の C 全図式の Yoneda 像は、同じ元の底余錐の始域。
方針：元の全始域境界と実引き戻し条件。規約：全射の等号。使われ方：実 comma の比較。 -/
lemma indConeEndpointBaseCone_source :
    joinInl (join T (Δ[0] : SSet.{u + 1})) Δ[0] ≫ indConeEndpointBaseCone V =
    (indConeEndpointRawFace V ≫
      pullback.fst (indYoneda κ C) (sliceOverProjection (indConeEndpointPoint κ D))) ≫
        indYoneda κ C := by
  rw [indConeEndpointBaseCone, ← Category.assoc, indConeEndpointSliceCone_source,
    Category.assoc, ← pullback.condition, Category.assoc]
end SerrePositivity.InfinityCategories.F2.Ind
