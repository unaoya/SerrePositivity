module

public import SerrePositivity.InfinityCategories.F1.Weighted.ConeDisplayTransport
public import SerrePositivity.InfinityCategories.F1.Weighted.ConeTotalFunctorImage

/-!
概要：豊穣関手で写した weighted 比較を、標準一点の実際の unstraightening 比較へ戻す。
方針：全空間の後合成自然性に、係数・始点・図式の表示変更の可換式を続ける。
規約：元の strictKanUnstraighteningComparison を標的に固定する。
使われ方：共通解像の実際の左脚と既存の反転比較との全単体の一致。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories
open HomotopyLimits

/-- 同じ係数像と表示変更を通すと、元の unstraightening 比較と共通 cone の後合成は一致。 -/
lemma weightedUnstraighteningComparison_functorImage
    {I : Type u} [SmallCategory I] {C : Type (u + 1)}
    [Category.{u} C] [SimplicialCategory C]
    (F : I ⥤ C) (R : EnrichedFunctor SSet.{u} C KanObject.{u}) (x : C)
    {G : I ⥤ KanObject.{u}} (hF : F ⋙ coherentEnrichedUnderlyingFunctor R = G)
    (hx : R.obj x = pointKanObject) :
    ((SSet.uliftFunctor.{u + 1, u}).map
      (weightedNerveMap (Functor.whiskerRight (weightedHomFunctorImage F R x) SSet.opFunctor)) ≫
      (SSet.uliftFunctor.{u + 1, u}).map (eqToHom (congrArg weightedNerve
        (congrArg₂ (fun D z => simplicialHomDiagram D z ⋙ SSet.opFunctor) hF hx)))) ≫
        strictKanUnstraighteningComparison G =
    weightedCoherentConeComparison F x ≫ coherentConeTotalFunctorImage F R x ≫
      eqToHom (congrArg (fun z => coherentConeTotal
        (strictCoherentDiagram (F ⋙ coherentEnrichedUnderlyingFunctor R))
          (coherentNerveVertex z)) hx) ≫
      (strictKanUnstraighteningIso (F ⋙ coherentEnrichedUnderlyingFunctor R)).hom ≫
      eqToHom (congrArg (fun D => leftUnstraightening (kanDiagramCoherentNerve D)) hF) := by
  rw [strictKanUnstraighteningIso_display hF hx]
  rw [← Category.assoc, weightedCoherentConeComparison_functorImage]
  rw [strictKanUnstraighteningComparison, Category.assoc, Category.assoc]
  have h := congrArg (fun k => (SSet.uliftFunctor.{u + 1, u}).map
    (weightedNerveMap (Functor.whiskerRight (weightedHomFunctorImage F R x) SSet.opFunctor)) ≫
      k ≫ (strictKanUnstraighteningIso G).hom)
    (weightedCoherentConeComparison_display hF hx)
  simpa only [Category.assoc] using h

end SerrePositivity.InfinityCategories
