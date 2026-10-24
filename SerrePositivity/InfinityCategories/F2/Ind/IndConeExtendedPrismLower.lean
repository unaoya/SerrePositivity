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
/-- 概要：補間した C 全族の下方制限は指定 G 自身の全図式。
方針：元の終点族の全下方境界を回収。規約：全係数の等号。使われ方：指定 G の回収。 -/
lemma indConeExtendedFamily_lower :
    (join T (Δ[0] : SSet.{u + 1}) ◁
      (SSet.uliftFunctor.{u + 1, u}).map (joinInl L (Δ[0] : SSet.{u}))) ≫
      indConeExtendedFamily V =
    diagramCommaOriginalFamily κ
      ((SSet.uliftFunctor.{u + 1, u}).map (joinInl L (Δ[0] : SSet.{u})) ≫ D) G.val := by
  rw [indConeExtendedFamily, ← Category.assoc, ← whiskerLeft_comp,
    uliftCoconeShapeIso_inl, ← Category.assoc _ V.endpoint,
    V.endpoint_lower, indConeLowerEndpointRaw_projection]
/-- 概要：補間した全円柱の下方制限は指定 G 自身の全円柱。
方針：再構成と二段持ち上げの全下方境界を回収。規約：全射の等号。使われ方：指定 G。 -/
lemma indConeExtendedPrism_lower :
    (join (join T (Δ[0] : SSet.{u + 1})) Δ[0] ◁
      (SSet.uliftFunctor.{u + 1, u}).map (joinInl L (Δ[0] : SSet.{u}))) ≫
      indConeExtendedPrism V =
    diagramCommaRightPrism κ
      ((SSet.uliftFunctor.{u + 1, u}).map (joinInl L (Δ[0] : SSet.{u})) ≫ D) G.val := by
  rw [indConeExtendedPrism, ← Category.assoc, ← whiskerLeft_comp,
    uliftCoconeShapeIso_inl, ← Category.assoc _ V.prism,
    V.lower, V.initial.lower_projection]
  rfl
end SerrePositivity.InfinityCategories.F2.Ind
