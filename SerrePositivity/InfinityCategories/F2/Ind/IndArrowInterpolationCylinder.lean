module

public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowInterpolationData

/-!
概要：構成した全円柱延長を元の終点の slice 引き戻しへ戻し、両全境界を回収する。
方針：円柱の宇宙比較と終点 comma 同型の逆を使う。
規約：元の円柱族 F と始点全錐の境界を厳密に保持。使われ方：全図式 comma への帰還。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {κ : Cardinal.{u}} {C A : SSet.{u}} [Quasicategory C]
  {D : (SSet.uliftFunctor.{u + 1, u}).obj (Δ[1] : SSet.{u}) ⟶ IndInfinity κ C}
  {q : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ diagramComma κ D}
  (V : IndArrowInterpolationData κ D q)

/-- 元の全円柱延長を、同じ終点の実 slice 引き戻しへ戻す。 -/
def indArrowInterpolationRawCylinder :
    (SSet.uliftFunctor.{u + 1, u}).obj (join A (Δ[0] : SSet.{u})) ⊗ Δ[1] ⟶
      pullback (indYoneda κ C)
        (sliceOverProjection (stdSimplex.δ 0 ≫ (liftedIntervalToSmall.{u} ≫ D))) :=
  inv (rightIntervalUniverseShape (join A (Δ[0] : SSet.{u}))) ≫
    V.extension ≫ (indArrowEndpointCommaIso κ D).inv

/-- 零端点の全族は、同じ元の始点全錐から作る引き戻しに厳密に一致。 -/
lemma indArrowInterpolationRawCylinder_source : SSet.ι₀ ≫ indArrowInterpolationRawCylinder V =
    indArrowSourceEndpointRaw κ D V.sourceCone := by
  have h := congrArg (fun f => f ≫ V.extension ≫ (indArrowEndpointCommaIso κ D).inv)
    (rightIntervalUniverseShape_inv_zero (join A (Δ[0] : SSet.{u})))
  have hs := congrArg (fun f => f ≫ (indArrowEndpointCommaIso κ D).inv) V.source
  have hs' : (SSet.uliftFunctor.{u + 1, u}).map SSet.ι₀ ≫ V.extension ≫
      (indArrowEndpointCommaIso κ D).inv = indArrowSourceEndpointRaw κ D V.sourceCone := by
    simpa only [indArrowSourceEndpointFamily, Category.assoc, Iso.hom_inv_id,
      Category.comp_id] using hs
  exact Eq.trans (by simpa only [indArrowInterpolationRawCylinder, Category.assoc] using h) hs'

/-- 元の全試験族側の制限は、同じ構成した円柱族 F の実引き戻しそのもの。 -/
lemma indArrowInterpolationRawCylinder_old :
    ((SSet.uliftFunctor.{u + 1, u}).map (joinInl A (Δ[0] : SSet.{u})) ▷ Δ[1]) ≫
      indArrowInterpolationRawCylinder V = indArrowEndpointRaw κ D q
        ((SSet.uliftFunctor.{u + 1, u}).map (joinInl A Δ[0]) ≫ V.sourceCone) V.slicePrism := by
  have h := congrArg (fun f => f ≫ V.extension ≫ (indArrowEndpointCommaIso κ D).inv)
    (rightIntervalUniverseShape_inv_naturality (joinInl A (Δ[0] : SSet.{u})))
  have ho := congrArg (fun f => inv (rightIntervalUniverseShape A) ≫ f ≫
    (indArrowEndpointCommaIso κ D).inv) V.old
  have ho' : inv (rightIntervalUniverseShape A) ≫
      (SSet.uliftFunctor.{u + 1, u}).map (joinInl A Δ[0] ▷ (Δ[1] : SSet.{u})) ≫
      V.extension ≫ (indArrowEndpointCommaIso κ D).inv = indArrowEndpointRaw κ D q
        ((SSet.uliftFunctor.{u + 1, u}).map (joinInl A Δ[0]) ≫ V.sourceCone) V.slicePrism := by
    simpa only [indArrowEndpointFamily, Category.assoc, Iso.hom_inv_id,
      Category.comp_id, IsIso.inv_hom_id_assoc] using ho
  exact Eq.trans (by simpa only [indArrowInterpolationRawCylinder, Category.assoc] using h) ho'

end SerrePositivity.InfinityCategories.F2.Ind
