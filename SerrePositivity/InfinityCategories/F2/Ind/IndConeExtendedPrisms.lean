module

public import SerrePositivity.InfinityCategories.F2.Ind.IndConeExtendedSliceData
public import SerrePositivity.InfinityCategories.F2.Ind.DiagramRightPrismFamily

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
/-- 概要：同じ拡張の C 全族を元の図式形状で読む。
方針：元の形状比較と第一射影。規約：全係数を保持。使われ方：元の実余錐の C 側。 -/
def indConeExtendedFamily : join T (Δ[0] : SSet.{u + 1}) ⊗
    (SSet.uliftFunctor.{u + 1, u}).obj (join L (Δ[0] : SSet.{u})) ⟶
      (SSet.uliftFunctor.{u + 1, u}).obj C :=
  (join T (Δ[0] : SSet.{u + 1}) ◁ (uliftCoconeShapeIso.{u, u + 1} L 0).hom) ≫
    V.endpoint ≫ pullback.fst (indYoneda κ C) (sliceOverProjection (indConeEndpointPoint κ D))
/-- 概要：同じ再構成の全円柱を元の図式形状で読む。
方針：元の形状比較と slice 射影。規約：全射を保持。使われ方：元の実余錐の全変換。 -/
def indConeExtendedPrism : join (join T (Δ[0] : SSet.{u + 1})) Δ[0] ⊗
    (SSet.uliftFunctor.{u + 1, u}).obj (join L (Δ[0] : SSet.{u})) ⟶ IndInfinity κ C :=
  (join (join T (Δ[0] : SSet.{u + 1})) Δ[0] ◁
    (uliftCoconeShapeIso.{u, u + 1} L 0).hom) ≫ V.prism ≫
      sliceOverProjection (indConeEndpointPoint κ D)
end SerrePositivity.InfinityCategories.F2.Ind
