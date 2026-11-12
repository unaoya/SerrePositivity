module

public import SerrePositivity.KST.Spectra.OrdinaryLoopUniversalSource
public import SerrePositivity.KST.Spectra.UniversalSourceIntervalNaturality

/-!
概要：通常円を内側にする一つの普遍区間から、通常 loop 値の実交換区間を回収する。
方針：源によらない anodyne 制限・同じ切断の移送を、厳密な curry 座標へ移す。
規約：元の普遍区間全体を使う。使われ方：元の通常円随伴への直接の移送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.KST.Spectra.OrdinaryLoopSource

/-- 同じ混合源の普遍区間を、全写像族へ移した実区間。 -/
abbrev sourceInterval (Z : PointedSimplicialSet.{u}) [KanComplex Z.right] :=
  UniversalSourceInterval.interval specification.{u} Z

/-- 元の通常 loop 値の二重 Kan loop の交換と反転を結ぶ、一つの普遍区間の像。 -/
def loopExchangeInterval (Z : PointedSimplicialSet.{u}) [KanComplex Z.right] :
    PointedMapping.VerticalPath (PointedObject.toPoint
      (LoopExchangePaths.doubleLoop (PointedObject.basedHom PointedSimplicialSet.circle.{u} Z)))
      (LoopExchangePaths.swap (PointedObject.basedHom PointedSimplicialSet.circle.{u} Z))
      (LoopExchangePaths.reversal (PointedObject.basedHom PointedSimplicialSet.circle.{u} Z)) := by
  have hs : LoopExchangePaths.swap (PointedObject.basedHom PointedSimplicialSet.circle.{u} Z) =
      (mappingIso Z).inv ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed swap.{u} Z ≫ (mappingIso Z).hom) := by
    rw [TwoLoopSource.mappingIso_pre_swap, Iso.inv_hom_id_assoc]
  have hr : LoopExchangePaths.reversal (PointedObject.basedHom PointedSimplicialSet.circle.{u} Z) =
      (mappingIso Z).inv ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed reversal.{u} Z ≫ (mappingIso Z).hom) := by
    rw [TwoLoopSource.mappingIso_pre_reversal, Iso.inv_hom_id_assoc]
  exact (((sourceInterval Z).basedPost (mappingIso Z).hom).pre
    (mappingIso Z).inv).changeEndpoints hs hr

/-- 元の通常 loop 値の辺全体は、同じ混合源区間の厳密な座標像。 -/
lemma loopExchangeInterval_path (Z : PointedSimplicialSet.{u}) [KanComplex Z.right] :
    (loopExchangeInterval Z).path =
      (((sourceInterval Z).basedPost (mappingIso Z).hom).pre (mappingIso Z).inv).path := rfl

end SerrePositivity.KST.Spectra.OrdinaryLoopSource
