module

public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.StrictKanUnstraighteningComparison

/-!
概要：weighted cone 比較の図式と始点の等号による表示変更を、同じ比較射へ揃える。
方針：二つの等号を消去し、恒等射の式に帰着する。
規約：表示変更後も既存の比較射そのものを保持する。
使われ方：共通 Hom 解像の左脚と元の反転 unstraightening 比較の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories
open HomotopyLimits

/-- 係数と cone 全空間の表示変更は、同じ元の weighted 比較と厳密に可換。 -/
lemma weightedCoherentConeComparison_display {I : Type u} [SmallCategory I]
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {F G : I ⥤ C} {x y : C} (hF : F = G) (hx : x = y) :
    (SSet.uliftFunctor.{v, u}).map (eqToHom (congrArg weightedNerve
      (congrArg₂ (fun D z => simplicialHomDiagram D z ⋙ SSet.opFunctor) hF hx))) ≫
      weightedCoherentConeComparison G y =
    weightedCoherentConeComparison F x ≫ eqToHom
      (congrArg₂ (fun D z => coherentConeTotal (strictCoherentDiagram D)
        (coherentNerveVertex z)) hF hx) := by
  subst G
  subst y
  simp only [eqToHom_refl, Category.comp_id]
  exact (congrArg (fun k => k ≫ weightedCoherentConeComparison F x)
    ((SSet.uliftFunctor.{v, u}).map_id _)).trans (Category.id_comp _)

/-- 始点を標準一点へ揃えてから図式を変える式は、一度の cone 表示変更と同じ射。 -/
lemma strictKanUnstraighteningIso_display {I : Type u} [SmallCategory I]
    {F G : I ⥤ KanObject.{u}} {x : KanObject.{u}} (hF : F = G) (hx : x = pointKanObject) :
    eqToHom (congrArg (fun z => coherentConeTotal (strictCoherentDiagram F)
      (coherentNerveVertex z)) hx) ≫ (strictKanUnstraighteningIso F).hom ≫
        eqToHom (congrArg (fun D => leftUnstraightening (kanDiagramCoherentNerve D)) hF) =
    eqToHom (congrArg₂ (fun D z => coherentConeTotal (strictCoherentDiagram D)
      (coherentNerveVertex z)) hF hx) ≫ (strictKanUnstraighteningIso G).hom := by
  subst G
  subst x
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

end SerrePositivity.InfinityCategories
