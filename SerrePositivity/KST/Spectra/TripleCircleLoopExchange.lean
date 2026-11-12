module

public import SerrePositivity.KST.Spectra.TripleCircleIntervalTransport

/-!
概要：三つの円の一つの普遍的区間を、loop 値の二重 loop の交換符号区間へ戻す。
方針：全写像族での区間を、同じ二度の curry 同型で共役する。
規約：標的ごとに成分から区間を選ばない。使われ方：Ω 条件に沿うトレース付き移送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.KST.Spectra.TripleCircle

/-- 一つの普遍的な源区間から得る、loop 値の二重 loop の同じ交換符号区間。 -/
def loopExchangeInterval (Z : PointedSimplicialSet.{u}) [KanComplex Z.right] :
    PointedMapping.VerticalPath (PointedObject.toPoint
      (LoopExchangePaths.doubleLoop (PointedObject.basedHom CirclePower.space.{u} Z)))
      (LoopExchangePaths.swap (PointedObject.basedHom CirclePower.space.{u} Z))
      (LoopExchangePaths.reversal (PointedObject.basedHom CirclePower.space.{u} Z)) := by
  have hs : LoopExchangePaths.swap (PointedObject.basedHom CirclePower.space.{u} Z) =
      (mappingIso Z).inv ≫
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed swap.{u} Z ≫ (mappingIso Z).hom) := by
    rw [mappingIso_pre_swap, Iso.inv_hom_id_assoc]
  have hr : LoopExchangePaths.reversal (PointedObject.basedHom CirclePower.space.{u} Z) =
      (mappingIso Z).inv ≫
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed reversal.{u} Z ≫ (mappingIso Z).hom) := by
    rw [mappingIso_pre_reversal, Iso.inv_hom_id_assoc]
  exact (((exchangeInterval Z).basedPost (mappingIso Z).hom).pre
    (mappingIso Z).inv).changeEndpoints hs hr

/-- 元の三重 loop の区間全体は、同じ全族の区間の厳密な curry 座標像。 -/
lemma loopExchangeInterval_path (Z : PointedSimplicialSet.{u}) [KanComplex Z.right] :
    (loopExchangeInterval Z).path =
      (((exchangeInterval Z).basedPost (mappingIso Z).hom).pre (mappingIso Z).inv).path := rfl

end SerrePositivity.KST.Spectra.TripleCircle
