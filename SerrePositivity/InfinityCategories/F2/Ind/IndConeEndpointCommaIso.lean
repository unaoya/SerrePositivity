module

public import SerrePositivity.InfinityCategories.F2.Ind.IndConeEndpointRaw
public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowEndpointCommaIso

/-!
概要：元の余錐図式の終点 comma を、元の同じ評価頂点の標準 comma へ戻す。
方針：終点の全点写像の等号を、実引き戻しの等号へ移す。
規約：元の C 側射影を厳密に保つ。
使われ方：既存の scalar comma の filtered 性を元の終点へ適用する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits SSet
open SerrePositivity.InfinityCategories.HomotopyLimits
open scoped Simplicial
universe u
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) {L C : SSet.{u}} [Quasicategory C]
  (D : (SSet.uliftFunctor.{u + 1, u}).obj (join L (Δ[0] : SSet.{u})) ⟶ IndInfinity κ C)
/-- 概要：余錐の宇宙比較は新しい終点の全包含を保持する。
方針：join の両因子の自然性。規約：元の包含。使われ方：元の指定終点への帰還。 -/
lemma indConeShape_inr :
    (SSet.uliftFunctor.{u + 1, u}).map (joinInr L (Δ[0] : SSet.{u})) ≫
      (uliftCoconeShapeIso.{u, u + 1} L 0).hom =
    (uliftStdSimplexIso.{u, u + 1} 0).hom ≫
      joinInr ((SSet.uliftFunctor.{u + 1, u}).obj L) Δ[0] := by
  unfold uliftCoconeShapeIso
  simp only [Iso.trans_hom, joinIso, ← Category.assoc, uliftJoinIso_inr, joinInr_joinMap]
/-- 概要：逆宇宙比較も新しい終点の全包含を保持する。
方針：同じ順比較の相殺。規約：元の包含。使われ方：指定終点への帰還。 -/
lemma indConeShape_inv_inr :
    joinInr ((SSet.uliftFunctor.{u + 1, u}).obj L) Δ[0] ≫
      (uliftCoconeShapeIso.{u, u + 1} L 0).inv =
    (uliftStdSimplexIso.{u, u + 1} 0).inv ≫
      (SSet.uliftFunctor.{u + 1, u}).map (joinInr L (Δ[0] : SSet.{u})) := by
  apply (cancel_epi (uliftStdSimplexIso.{u, u + 1} 0).hom).mp
  rw [← Category.assoc, ← indConeShape_inr, Category.assoc, Iso.hom_inv_id,
    Category.comp_id, Iso.hom_inv_id_assoc]
/-- 概要：正規化した終点は元の評価頂点の全点写像そのもの。
方針：全単体作用の同定。規約：点写像の等号。使われ方：実 comma の表示変更。 -/
lemma indConeEndpoint_point : indConeEndpointPoint κ D =
    SSet.yonedaEquiv.symm (D.app (Opposite.op ⦋0⦌) (ULift.up (coneApex L))) := by
  rw [indConeEndpointPoint, indConeNormalizedDiagram, ← Category.assoc,
    indConeShape_inv_inr]
  have he : joinInr L (Δ[0] : SSet.{u}) = SSet.yonedaEquiv.symm (coneApex L) := by
    apply SSet.yonedaEquiv.injective
    rw [Equiv.apply_symm_apply]
    have hp : (stdSimplex.obj₀Equiv.symm 0 : (Δ[0] : SSet.{u}) _⦋0⦌) =
        SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})) := by
      apply SSet.stdSimplex.ext
      intro i
      apply Fin.ext
      omega
    exact congrArg (fun x ↦ (joinInr L (Δ[0] : SSet.{u})).app (Opposite.op ⦋0⦌) x) hp.symm
  rw [he, HomotopyLimits.uliftYonedaMap, SSet.yonedaEquiv_symm_comp]
/-- 概要：同じ元の終点上の実 comma と標準 scalar comma の厳密な同型。
方針：全点写像の等号を移す。規約：全引き戻しを保持。使われ方：終点の実拡張。 -/
def indConeEndpointCommaIso :
    pullback (indYoneda κ C) (sliceOverProjection (indConeEndpointPoint κ D)) ≅
      leftKanShape (indYoneda κ C)
        (D.app (Opposite.op ⦋0⦌) (ULift.up (coneApex L))) :=
  eqToIso (congrArg (fun p ↦ pullback (indYoneda κ C) (sliceOverProjection p))
    (indConeEndpoint_point κ D))
/-- 概要：終点の表示変更は元の C 全図式を厳密に保持する。
方針：同じ引き戻しの射影を照合。規約：全射の等号。使われ方：元の全族への帰還。 -/
lemma indConeEndpointCommaIso_projection : (indConeEndpointCommaIso κ D).hom ≫
    leftKanProjection (indYoneda κ C)
      (D.app (Opposite.op ⦋0⦌) (ULift.up (coneApex L))) =
    pullback.fst (indYoneda κ C) (sliceOverProjection (indConeEndpointPoint κ D)) :=
  slicePullbackTransport_projection (indYoneda κ C) (indConeEndpoint_point κ D)
end SerrePositivity.InfinityCategories.F2.Ind
