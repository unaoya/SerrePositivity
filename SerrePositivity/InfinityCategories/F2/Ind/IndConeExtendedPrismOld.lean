module

public import SerrePositivity.InfinityCategories.F2.Ind.IndConeExtendedPrismBoundary

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
/-- 概要：補間した元の C 全族の旧族制限は元の q の全図式そのもの。
方針：元の終点族の境界と宇宙比較の往復。規約：全射の等号。使われ方：旧族の回収。 -/
lemma indConeExtendedFamily_old :
    (joinInl T (Δ[0] : SSet.{u + 1}) ▷
      (SSet.uliftFunctor.{u + 1, u}).obj (join L (Δ[0] : SSet.{u}))) ≫
      indConeExtendedFamily V = diagramCommaOriginalFamily κ D q := by
  rw [indConeExtendedFamily, ← Category.assoc, ← whisker_exchange, Category.assoc,
    ← Category.assoc _ V.endpoint, V.endpoint_old,
    indConeEndpointRaw_projection, ← Category.assoc, ← whiskerLeft_comp,
    Iso.hom_inv_id, whiskerLeft_id, Category.id_comp]
/-- 概要：補間した元の全円柱の旧族制限は元の q の全円柱そのもの。
方針：元の slice 全円柱の固定と宇宙比較の往復。規約：全射の等号。使われ方：旧族の回収。 -/
lemma indConeExtendedPrism_old :
    (joinMap (joinInl T (Δ[0] : SSet.{u + 1})) (𝟙 Δ[0]) ▷
      (SSet.uliftFunctor.{u + 1, u}).obj (join L (Δ[0] : SSet.{u}))) ≫
      indConeExtendedPrism V = diagramCommaRightPrism κ D q := by
  rw [indConeExtendedPrism, ← Category.assoc, ← whisker_exchange, Category.assoc,
    ← Category.assoc _ V.prism, V.old, V.initial.projection,
    indConeOriginalPrism, ← Category.assoc, ← whiskerLeft_comp,
    Iso.hom_inv_id, whiskerLeft_id, Category.id_comp]
end SerrePositivity.InfinityCategories.F2.Ind
