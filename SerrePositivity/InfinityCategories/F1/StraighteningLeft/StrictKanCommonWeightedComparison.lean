module

public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.StrictKanCommonUnstraightening
public import SerrePositivity.InfinityCategories.F1.Weighted.UnstraighteningFunctorImage
public import SerrePositivity.InfinityCategories.F1.Categories.OppositeKanUnstraightening

/-!
概要：共通 Hom 解像の weighted 係数を、元の反転 unstraightening 比較の同じ係数へ写す。
方針：実際の反転 Hom の作用に図式と一点の表示変更を続け、既存の係数同型を使う。
規約：元の oppositeKanUnstraighteningComparison との合成を射の等式で記録する。
使われ方：weighted nerve の復元同型と反転 unstraightening の共同実現の接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories
open HomotopyLimits

local instance : ∀ X Y : EdgewiseEnrichedObject KanObject.{u},
    KanComplex (SimplicialCategory.sHom X Y) := fun X Y =>
  inferInstanceAs (KanComplex (edgewiseSubdivision (SimplicialCategory.sHom X.val Y.val)))

variable {I : Type u} [SmallCategory I] (F : I ⥤ KanObject.{u})

/-- 共通 weighted 係数を、元の反転図式の一点からの反転 Hom 係数へ写す実際の射。 -/
def strictKanCommonOppositeWeightedImage :
    (SSet.uliftFunctor.{u + 1, u}).obj (weightedNerve
      (simplicialHomDiagram (strictKanCommonDiagram F) edgewisePointKanObject ⋙ SSet.opFunctor)) ⟶
    (SSet.uliftFunctor.{u + 1, u}).obj (weightedNerve
      (simplicialHomDiagram (F ⋙ kanObjectOpFunctor) pointKanObject ⋙ SSet.opFunctor)) :=
  (SSet.uliftFunctor.{u + 1, u}).map (weightedNerveMap (Functor.whiskerRight
    (weightedHomFunctorImage (strictKanCommonDiagram F) edgewiseOppositeKanEnriched
      edgewisePointKanObject) SSet.opFunctor)) ≫
  (SSet.uliftFunctor.{u + 1, u}).map (eqToHom (congrArg weightedNerve
    (congrArg₂ (fun D z => simplicialHomDiagram D z ⋙ SSet.opFunctor)
      (strictKanCommonDiagram_opposite F) kanObjectOpFunctor_point)))

/-- 同じ共通 weighted 係数から、元の weighted nerve の係数へのパラメーター射。 -/
def strictKanCommonWeightedParameterMap :
    (SSet.uliftFunctor.{u + 1, u}).obj (weightedNerve
      (simplicialHomDiagram (strictKanCommonDiagram F) edgewisePointKanObject ⋙ SSet.opFunctor)) ⟶
    (SSet.uliftFunctor.{u + 1, u}).obj (weightedNerve (F ⋙ kanObjectForget)) :=
  strictKanCommonOppositeWeightedImage F ≫
    (SSet.uliftFunctor.{u + 1, u}).map (oppositePointHomWeightedIso F).hom

/-- 共通 cone の左脚は、元の反転図式の標準比較を同じ weighted 係数で引き戻した射。 -/
lemma strictKanCommonOppositeWeightedImage_compare :
    strictKanCommonOppositeWeightedImage F ≫
      strictKanUnstraighteningComparison (F ⋙ kanObjectOpFunctor) =
    weightedCoherentConeComparison (strictKanCommonDiagram F) edgewisePointKanObject ≫
      strictKanCommonUnstraighteningOpposite F := by
  have h := weightedUnstraighteningComparison_functorImage (strictKanCommonDiagram F)
    edgewiseOppositeKanEnriched edgewisePointKanObject (strictKanCommonDiagram_opposite F)
    kanObjectOpFunctor_point
  simpa only [strictKanCommonOppositeWeightedImage, strictKanCommonUnstraighteningOpposite,
    edgewisePointedUnstraighteningOpposite, edgewiseOppositePointConeUnstraighteningIso,
    Iso.trans_hom, eqToIso.hom, Category.assoc] using h

/-- 元の反転 unstraightening 比較との合成は、同じ共通 weighted cone の左脚に厳密に一致。 -/
lemma strictKanCommonWeightedParameterMap_compare :
    strictKanCommonWeightedParameterMap F ≫ oppositeKanUnstraighteningComparison F =
    weightedCoherentConeComparison (strictKanCommonDiagram F) edgewisePointKanObject ≫
      strictKanCommonUnstraighteningOpposite F := by
  rw [strictKanCommonWeightedParameterMap, oppositeKanUnstraighteningComparison, Category.assoc,
    ← Category.assoc ((SSet.uliftFunctor.{u + 1, u}).map (oppositePointHomWeightedIso F).hom),
    ← Functor.map_comp, Iso.hom_inv_id, (SSet.uliftFunctor.{u + 1, u}).map_id, Category.id_comp]
  exact strictKanCommonOppositeWeightedImage_compare F

/-- 同じ係数パラメーター射は、元と共通解像の同じ持ち上げた底を厳密に保つ。 -/
lemma strictKanCommonWeightedParameterMap_projection :
    strictKanCommonWeightedParameterMap F ≫
      (SSet.uliftFunctor.{u + 1, u}).map (weightedNerveProjection (F ⋙ kanObjectForget)) =
    (SSet.uliftFunctor.{u + 1, u}).map (weightedNerveProjection
      (simplicialHomDiagram (strictKanCommonDiagram F) edgewisePointKanObject ⋙
        SSet.opFunctor)) := by
  have h := congrArg (fun k => k ≫
    leftUnstraighteningProjection (kanDiagramCoherentNerve (F ⋙ kanObjectOpFunctor)))
    (strictKanCommonWeightedParameterMap_compare F)
  rw [Category.assoc, oppositeKanUnstraighteningComparison_projection, Category.assoc,
    strictKanCommonUnstraighteningOpposite_projection, weightedCoherentConeComparison_over] at h
  exact h

/-- 共通係数から元の weighted nerve への同じパラメーター射そのものは前合成同値。 -/
lemma strictKanCommonWeightedParameterMap_isPrecompositionEquivalence :
    IsPrecompositionEquivalence (strictKanCommonWeightedParameterMap F) := by
  have h := (weightedCoherentConeComparison_isPrecompositionEquivalence
    (strictKanCommonDiagram F) edgewisePointKanObject).comp
      (strictKanCommonUnstraighteningOpposite_isPrecompositionEquivalence F)
  rw [← strictKanCommonWeightedParameterMap_compare] at h
  exact (oppositeKanUnstraighteningComparison_isPrecompositionEquivalence F).cancel_right h

end SerrePositivity.InfinityCategories
