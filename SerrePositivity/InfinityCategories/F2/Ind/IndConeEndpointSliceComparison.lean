module

public import SerrePositivity.InfinityCategories.F2.Ind.IndConeEndpointSliceConeTip
public import SerrePositivity.InfinityCategories.F2.Ind.ConePointSliceComparison
public import SerrePositivity.InfinityCategories.F2.Ind.RelativeFunctorVertexIsoProjection

/-!
概要：元の終点 slice 族と再構成された終点 slice 族を、同じ全底上で比較する。
方針：同じ元の点の恒等頂点で終わる全余錐の相対比較を適用する。
規約：元の底図式と指定終点を固定した比較同型を保持する。
使われ方：元の実終点 comma 内の全族の比較への移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {κ : Cardinal.{u}} {L C : SSet.{u}} [Quasicategory C]
  {D : (SSet.uliftFunctor.{u + 1, u}).obj (join L (Δ[0] : SSet.{u})) ⟶ IndInfinity κ C}
  {T : SSet.{u + 1}} {q : T ⟶ diagramComma κ D}
  {G : JoinCocone (q ≫ diagramCommaRestriction κ D (joinInl L (Δ[0] : SSet.{u})))}
  (V : IndConeExtendedSliceData κ D q G)
/-- 概要：元の全底を固定して、終点の元の slice 族と再構成した評価族を比較する。
方針：同じ恒等終点で終わる全余錐の相対比較。規約：元の底。使われ方：極大点の共終性。 -/
def indConeEndpointSliceRelativeIso :
    VertexIso
      (relativeFunctorVertex (sliceOverProjection (indConeEndpointPoint κ D))
        (joinInl (join T (Δ[0] : SSet.{u + 1})) Δ[0] ≫ indConeEndpointBaseCone V)
        (joinInl (join T (Δ[0] : SSet.{u + 1})) Δ[0] ≫ indConeEndpointSliceCone V)
        (by rw [Category.assoc]; rfl))
      (relativeFunctorVertex (sliceOverProjection (indConeEndpointPoint κ D))
        (joinInl (join T (Δ[0] : SSet.{u + 1})) Δ[0] ≫ indConeEndpointBaseCone V)
        (sliceOverCurry (indConeEndpointBaseCone V) (indConeEndpointBaseCone_tip V))
        (sliceOverCurry_projection _ _)) :=
  conePointSliceBoundaryRelativeIso (indConeEndpointPoint κ D) (indConeEndpointBaseCone V)
    (indConeEndpointBaseCone_tip V) (indConeEndpointSliceCone V) rfl
    (indConeEndpointSliceCone_tip_uncurry V)
/-- 概要：同じ元の底を固定した終点面の比較を、元の全 slice 族の同型として読む。
方針：元の相対関手空間の包含。規約：同じ全族。使われ方：実終点 comma への比較の移送。 -/
def indConeEndpointSliceFunctorIso : FunctorIso
    (joinInl (join T (Δ[0] : SSet.{u + 1})) Δ[0] ≫ indConeEndpointSliceCone V)
    (sliceOverCurry (indConeEndpointBaseCone V) (indConeEndpointBaseCone_tip V)) :=
  relativeFunctorVertexIsoImage _ _ _ _ _ _ (indConeEndpointSliceRelativeIso V)
end SerrePositivity.InfinityCategories.F2.Ind
