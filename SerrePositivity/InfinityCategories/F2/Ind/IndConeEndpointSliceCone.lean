module

public import SerrePositivity.InfinityCategories.F2.Ind.IndConeExtendedPrismBoundary
public import SerrePositivity.InfinityCategories.F2.Ind.TensorRightPoint

/-!
概要：元の全補間の終点面を、同じ実 comma の全族と slice の全余錐として取り出す。
方針：同じ元の余錐点で右因子を固定し、元の全始域境界を制限する。
規約：元の点写像・底の全余錐・C 全係数を保持する。
使われ方：元の終点族と再構成された極大点評価の比較。
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
/-- 概要：元の実終点 comma の全拡張を同じ終点面で読む。
方針：元の余錐点で右因子を固定。規約：元の全射。使われ方：新しい極大点の評価比較。 -/
def indConeEndpointRawFace : join T (Δ[0] : SSet.{u + 1}) ⟶
    pullback (indYoneda κ C) (sliceOverProjection (indConeEndpointPoint κ D)) :=
  tensorRightPoint (join T (Δ[0] : SSet.{u + 1}))
    (joinInr ((SSet.uliftFunctor.{u + 1, u}).obj L) Δ[0]) ≫ V.endpoint
/-- 概要：再構成した全 slice 円柱の同じ終点面。
方針：元の余錐点で右因子を固定。規約：全射を保持。使われ方：同じ元の底上での比較。 -/
def indConeEndpointSliceCone : join (join T (Δ[0] : SSet.{u + 1})) Δ[0] ⟶
    sliceOver (indConeEndpointPoint κ D) :=
  tensorRightPoint (join (join T (Δ[0] : SSet.{u + 1})) Δ[0])
    (joinInr ((SSet.uliftFunctor.{u + 1, u}).obj L) Δ[0]) ≫ V.prism
/-- 概要：同じ終点面の元の全底余錐。
方針：元の slice 射影。規約：全射を保持。使われ方：同じ底を固定する相対比較。 -/
def indConeEndpointBaseCone : join (join T (Δ[0] : SSet.{u + 1})) Δ[0] ⟶
    IndInfinity κ C :=
  indConeEndpointSliceCone V ≫ sliceOverProjection (indConeEndpointPoint κ D)
/-- 概要：再構成した終点面の始域は元の実終点族の同じ slice 成分。
方針：元の全始域境界と点制限の自然性。規約：全射の等号。使われ方：終点族の比較。 -/
lemma indConeEndpointSliceCone_source :
    joinInl (join T (Δ[0] : SSet.{u + 1})) Δ[0] ≫ indConeEndpointSliceCone V =
    indConeEndpointRawFace V ≫
      pullback.snd (indYoneda κ C) (sliceOverProjection (indConeEndpointPoint κ D)) := by
  rw [indConeEndpointSliceCone, ← Category.assoc, tensorRightPoint_naturality,
    Category.assoc, V.source, indConeEndpointRawFace, Category.assoc]
end SerrePositivity.InfinityCategories.F2.Ind
