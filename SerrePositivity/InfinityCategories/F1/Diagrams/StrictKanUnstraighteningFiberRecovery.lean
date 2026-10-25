module

public import SerrePositivity.InfinityCategories.F1.Coherent.PointedFiberValueNormalization
public import SerrePositivity.InfinityCategories.F1.Weighted.NerveMapComparison
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.DirectKanCoefficients
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.SmallLeftUnstraighteningFiber

/-!
概要：strict な Kan 図式の実比較の fiber 座標を、既存の値回収に照合する。
方針：元の coherent cone 比較の fiber 因子分解と、同じ頂点表示の正規化を使う。
規約：元の比較射と元の値回収射を共に固定する。
使われ方：Ind-S (5) の単位回収の unstraightening 側。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
open HomotopyLimits

/-- 同じ全空間の表示移送を fiber に制限すると、元の左 coslice fiber の正規化になる。 -/
lemma strictKanUnstraighteningIso_fiber_normalization
    {I : Type u} [Category.{u} I] (F : I ⥤ KanObject.{u}) (c : I) :
    vertexFiberMap
      (coherentConeProjection (strictCoherentDiagram F) (coherentNerveVertex pointKanObject))
      (leftUnstraighteningProjection (kanDiagramCoherentNerve F))
      (strictKanUnstraighteningIso F).hom (strictKanUnstraighteningIso_projection F)
      (ULift.up (nerveVertex c)) ≫
      (leftUnstraighteningFiberIso (kanDiagramCoherentNerve F) (ULift.up (nerveVertex c))).hom ≫
      eqToHom (congrArg (vertexFiber pointedSpaceProjection) (kanDiagramCoherentNerve_vertex F c)) =
    (weightedConeTargetFiberIso F pointKanObject c).hom ≫
      coherentPointedFiberNormalization (F.obj c) := by
  rw [coherentPointedFiberNormalization_eq]
  rfl

/-- 実際の直値 unstraightening 比較の全 fiber 制限は、同じ左 Hom 比較に因子分解する。 -/
lemma reversedWeightedKanUnstraighteningComparison_fiber_normalization
    {I : Type u} [Category.{u} I] (F : I ⥤ KanObject.{u}) (c : I) :
    (SSet.uliftFunctor.{u + 1, u}).map
        (weightedNerveFiberMap (F ⋙ kanObjectOpFunctor ⋙ kanObjectForget) c) ≫
      (uliftVertexFiberIso _ (nerveVertex c)).hom ≫
      vertexFiberMap _ _ (reversedWeightedKanUnstraighteningComparison F)
        (reversedWeightedKanUnstraighteningComparison_projection F) (ULift.up (nerveVertex c)) ≫
      (leftUnstraighteningFiberIso (kanDiagramCoherentNerve F) (ULift.up (nerveVertex c))).hom ≫
      eqToHom (congrArg (vertexFiber pointedSpaceProjection) (kanDiagramCoherentNerve_vertex F c)) =
    (SSet.uliftFunctor.{u + 1, u}).map ((directPointHomDiagramIso F).inv.app c) ≫
      coherentCosliceFiberComparison pointKanObject (F.obj c) ≫
      coherentPointedFiberNormalization (F.obj c) := by
  have h := weightedCoherentConeFiberMap_factorization F pointKanObject c
  rw [weightedConstantCosliceFiberMap_eq] at h
  calc
    _ = (SSet.uliftFunctor.{u + 1, u}).map ((directPointHomDiagramIso F).inv.app c) ≫
        (weightedConeSourceFiberIso F pointKanObject c).hom ≫
        weightedCoherentConeFiberMap F pointKanObject (ULift.up (nerveVertex c)) ≫
        (weightedConeTargetFiberIso F pointKanObject c).hom ≫
        coherentPointedFiberNormalization (F.obj c) := by
      rw [← strictKanUnstraighteningIso_fiber_normalization F c]
      have hs : (SSet.uliftFunctor.{u + 1, u}).map
          (weightedNerveFiberMap (F ⋙ kanObjectOpFunctor ⋙ kanObjectForget) c) ≫
          (uliftVertexFiberIso _ (nerveVertex c)).hom ≫
          vertexFiberMap _ _ (reversedWeightedKanUnstraighteningComparison F)
            (reversedWeightedKanUnstraighteningComparison_projection F) (ULift.up (nerveVertex c)) =
        (SSet.uliftFunctor.{u + 1, u}).map ((directPointHomDiagramIso F).inv.app c) ≫
          (weightedConeSourceFiberIso F pointKanObject c).hom ≫
          weightedCoherentConeFiberMap F pointKanObject (ULift.up (nerveVertex c)) ≫
          vertexFiberMap _ _ (strictKanUnstraighteningIso F).hom
            (strictKanUnstraighteningIso_projection F) (ULift.up (nerveVertex c)) := by
        apply vertexFiber_hom_ext
        simp only [weightedCoherentConeFiberMap, Category.assoc,
          reassoc_of% vertexFiberMap_ι]
        erw [reassoc_of% (weightedConeSourceFiberIso_hom_ι F pointKanObject c)]
        erw [vertexFiberMap_ι,
          reassoc_of% (SerrePositivity.InfinityCategories.uliftVertexFiberIso_hom_ι.{u, u + 1}
            (weightedNerveProjection (F ⋙ kanObjectOpFunctor ⋙ kanObjectForget)) (nerveVertex c))]
        have hη := congrArg (fun k => k ≫ vertexFiberι _ (nerveVertex c))
          (weightedNerveMap_fiber_naturality (directPointHomDiagramIso F).inv c)
        change weightedNerveConstantLift (F ⋙ kanObjectOpFunctor ⋙ kanObjectForget) c ≫
            weightedNerveMap (directPointHomDiagramIso F).inv =
          (directPointHomDiagramIso F).inv.app c ≫
            weightedNerveConstantLift (simplicialHomDiagram F pointKanObject ⋙ SSet.opFunctor) c at hη
        simp only [← Category.assoc, ← Functor.map_comp]
        change (SSet.uliftFunctor.{u + 1, u}).map
            (weightedNerveConstantLift (F ⋙ kanObjectOpFunctor ⋙ kanObjectForget) c) ≫
              reversedWeightedKanUnstraighteningComparison F = _
        unfold reversedWeightedKanUnstraighteningComparison strictKanUnstraighteningComparison
        change _ = _
        simp only [← Category.assoc, ← Functor.map_comp]
        change (SSet.uliftFunctor.{u + 1, u}).map
            (weightedNerveConstantLift (F ⋙ kanObjectOpFunctor ⋙ kanObjectForget) c ≫
              weightedNerveMap (directPointHomDiagramIso F).inv) ≫ _ = _
        rw [hη]
      simpa only [Category.assoc] using congrArg (fun k => k ≫
        (leftUnstraighteningFiberIso (kanDiagramCoherentNerve F) (ULift.up (nerveVertex c))).hom ≫
        eqToHom (congrArg (vertexFiber pointedSpaceProjection)
          (kanDiagramCoherentNerve_vertex F c))) hs
    _ = _ := by rw [reassoc_of% h]

/-- 元の strict 図式の値回収は、同じ頂点表示移送に続く標準 pointed-space 値回収。 -/
lemma kanDiagramUnstraighteningFiberValue_normalization
    {I : Type u} [Category.{u} I] (F : I ⥤ KanObject.{u}) (c : I) :
    (leftUnstraighteningFiberValueEquivalence
      (kanDiagramCoherentNerve F) (ULift.up (nerveVertex c))).hom =
    (leftUnstraighteningFiberIso (kanDiagramCoherentNerve F) (ULift.up (nerveVertex c))).hom ≫
      eqToHom (congrArg (vertexFiber pointedSpaceProjection) (kanDiagramCoherentNerve_vertex F c)) ≫
      (pointedSpaceFiberValueEquivalence (spaceInfinityVertex (F.obj c))).hom := by
  have h := pointedSpaceFiberValueEquivalence_endpoint_naturality
    (kanDiagramCoherentNerve_vertex F c)
  simp only [eqToHom_refl, Category.comp_id] at h
  exact congrArg (fun k =>
    (leftUnstraighteningFiberIso (kanDiagramCoherentNerve F) (ULift.up (nerveVertex c))).hom ≫ k) h

end SerrePositivity.InfinityCategories
