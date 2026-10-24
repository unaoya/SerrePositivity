module

public import SerrePositivity.InfinityCategories.F2.Ind.IndConeExtendedPrisms

/-!
概要：全拡張データの元の C 全族と全円柱を、元の小さい図式形状の表示へ戻す。
方針：元の余錐形状の宇宙比較で前合成し、元の引き戻しと slice の射影を使う。
規約：新しい同型や持ち上げを選ばず、同じ全射を保持する。
使われ方：同じ元の diagram comma に余錐族を構成する。
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
/-- 概要：元の D 側面は全 slice 円柱の再構成でも厳密に固定される。
方針：旧族の全円柱の同じ終端側面を制限。規約：全射の等号。使われ方：元の D の回収。 -/
lemma indConeExtendedSlice_tip :
    (joinInr (join T (Δ[0] : SSet.{u + 1})) Δ[0] ▷
      join ((SSet.uliftFunctor.{u + 1, u}).obj L) Δ[0]) ≫ V.prism =
    CartesianMonoidalCategory.snd (Δ[0] : SSet.{u + 1})
      (join ((SSet.uliftFunctor.{u + 1, u}).obj L) Δ[0]) ≫
        coneTerminalSliceSection (indConeNormalizedDiagram κ D) := by
  have h := congrArg (fun W ↦ (joinInr T (Δ[0] : SSet.{u + 1}) ▷
    join ((SSet.uliftFunctor.{u + 1, u}).obj L) Δ[0]) ≫ W) V.old
  rw [← Category.assoc, ← comp_whiskerRight, joinInr_joinMap, Category.id_comp] at h
  exact h.trans V.initial.tip
/-- 概要：再構成した元の全円柱の旧族側は同じ C 全図式の Yoneda 像。
方針：元の引き戻し条件と再構成の全始域境界。規約：全射の等号。使われ方：実余錐。 -/
lemma indConeExtendedPrism_source :
    (joinInl (join T (Δ[0] : SSet.{u + 1})) Δ[0] ▷
      (SSet.uliftFunctor.{u + 1, u}).obj (join L (Δ[0] : SSet.{u}))) ≫
      indConeExtendedPrism V = indConeExtendedFamily V ≫ indYoneda κ C := by
  rw [indConeExtendedPrism, ← Category.assoc, ← whisker_exchange,
    Category.assoc, ← Category.assoc _ V.prism, V.source,
    Category.assoc, ← pullback.condition]
  simp only [indConeExtendedFamily, Category.assoc]
/-- 概要：再構成した元の全円柱の終端側面は指定 D そのもの。
方針：同じ全 D 切断の射影と元の宇宙比較の往復。規約：全射の等号。使われ方：実余錐。 -/
lemma indConeExtendedPrism_tip :
    (joinInr (join T (Δ[0] : SSet.{u + 1})) Δ[0] ▷
      (SSet.uliftFunctor.{u + 1, u}).obj (join L (Δ[0] : SSet.{u}))) ≫
      indConeExtendedPrism V =
    CartesianMonoidalCategory.snd (Δ[0] : SSet.{u + 1})
      ((SSet.uliftFunctor.{u + 1, u}).obj (join L (Δ[0] : SSet.{u}))) ≫ D := by
  have hp : coneTerminalSliceSection (indConeNormalizedDiagram κ D) ≫
      sliceOverProjection (indConeEndpointPoint κ D) = indConeNormalizedDiagram κ D := by
    convert coneTerminalSliceSection_projection (indConeNormalizedDiagram κ D) using 1 <;> rfl
  rw [indConeExtendedPrism, ← Category.assoc, ← whisker_exchange,
    Category.assoc, ← Category.assoc _ V.prism, indConeExtendedSlice_tip,
    Category.assoc, hp,
    indConeNormalizedDiagram,
    ← Category.assoc, CartesianMonoidalCategory.whiskerLeft_snd]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
end SerrePositivity.InfinityCategories.F2.Ind
