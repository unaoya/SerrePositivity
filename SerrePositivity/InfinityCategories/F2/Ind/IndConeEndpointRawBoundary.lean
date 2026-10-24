module

public import SerrePositivity.InfinityCategories.F2.Ind.IndConeEndpointRaw
public import SerrePositivity.InfinityCategories.F2.Ind.DiagramCommaOriginalFamilyNaturality

/-!
概要：元の q と下方余錐 G の二段持ち上げを、同じ終点上の実 comma の全族へ移す。
方針：元の C 全図式と、構成した同じ slice の全射を厳密に引き戻す。
規約：元の全係数と全円柱を保持し、終点の表示変更はまだ行わない。
使われ方：一般の余錐積への実拡張に渡す、互換な二つの全境界の構成。
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
  (V : IndConeSliceInterpolationData κ D q G)

/-- 概要：元の q と指定した下方余錐 G は、同じ実終点 comma で全境界が一致する。
方針：C 全図式の自然性と二段 slice の境界を照合する。
規約：射影後の同値でなく全射の等号。使われ方：実 comma の余錐積への拡張。 -/
lemma indConeEndpointRaw_boundary :
    (T ◁ joinInl ((SSet.uliftFunctor.{u + 1, u}).obj L) Δ[0]) ≫
      indConeEndpointRaw V =
    (joinInl T (Δ[0] : SSet.{u + 1}) ▷
      (SSet.uliftFunctor.{u + 1, u}).obj L) ≫ indConeLowerEndpointRaw V := by
  apply pullback.hom_ext
  · simp only [Category.assoc, indConeEndpointRaw_projection,
      indConeLowerEndpointRaw_projection]
    rw [← Category.assoc, ← whiskerLeft_comp, uliftCoconeShapeIso_inv_inl,
      diagramCommaOriginalFamily_restrict, diagramCommaOriginalFamily_precomp, G.property]
  · simp only [Category.assoc, indConeEndpointRaw_slice, indConeLowerEndpointRaw_slice]
    rw [← Category.assoc, whisker_exchange, Category.assoc, V.lower_boundary]
    simp only [← Category.assoc, ← comp_whiskerRight, joinInl_joinMap]

end SerrePositivity.InfinityCategories.F2.Ind
