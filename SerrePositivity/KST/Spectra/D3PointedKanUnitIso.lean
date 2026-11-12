module

public import SerrePositivity.KST.Spectra.D3PointedKanParameterVertex
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength

/-!
概要：単位パラメータの内部 Hom と恒等関手を、同じ標準単位同型で全 Hom 上比較する。
方針：抽象閉圏の評価と豊穣合成を単位子で照合し、実 Kan 豊穣自然変換へ代入する。
規約：通常射だけの自然性ではなく、元の全 Hom の厳密正方形を使う。
使われ方：実端点 loop 図式族の終点を元の Kan 入力へ接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF

section
variable {C : Type v} [Category.{w} C] [MonoidalCategory C] [MonoidalClosed C]

/-- 元の標準単位同型は、単位パラメータでの同じ評価射。 -/
lemma d3Closed_curry_unit {T Y : C} (f : (𝟙_ C) ⊗ T ⟶ Y) :
    curry f ≫ (unitIsoSelf (X := Y)).hom = (λ_ T).inv ≫ f := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.unit_evaluation, leftUnitor_inv_naturality_assoc,
    whiskerLeft_curry_ihom_ev_app]

/-- 単位内部 Hom の全作用と標準単位同型の、抽象閉圏上の厳密自然性。 -/
lemma d3Closed_unit_action (X Y : C) :
    curry (MonoidalClosed.comp (𝟙_ C) X Y) ≫
      (ihom ((ihom (𝟙_ C)).obj X)).map (unitIsoSelf (X := Y)).hom =
        (MonoidalClosed.pre (unitIsoSelf (X := X)).hom).app Y := by
  apply uncurry_injective
  rw [uncurry_natural_right, uncurry_curry, uncurry_eq, id_tensor_pre_app_comp_ev]
  rw [MonoidalClosed.comp_eq, d3Closed_curry_unit, compTranspose_eq,
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.unit_evaluation, comp_whiskerRight]
  rw [← Category.assoc, ← leftUnitor_inv_tensor_id, tensorHom_id]
  simp only [Category.assoc]
end


local instance d3UnitPointedCategory : SimplicialCategory PointedSimplicialSet.{u} :=
  PointedEnrichment.simplicialCategory

/-- 同じ標準単位同型は、元の Kan 全 Hom に関する厳密な豊穣正方形。 -/
lemma d3PointedKanUnit_whiskered (X Y : PointedKanObject.{u}) :
    (d3PointedKanIhom (𝟙_ PointedSimplicialSet.{u})).map X Y ≫
      eHomWhiskerLeft SSet ((d3PointedKanIhom (𝟙_ PointedSimplicialSet.{u})).obj X)
        (ObjectProperty.homMk (unitIsoSelf (X := Y.obj)).hom :
          (d3PointedKanIhom (𝟙_ PointedSimplicialSet.{u})).obj Y ⟶ Y) =
      (EnrichedFunctor.id SSet PointedKanObject.{u}).map X Y ≫
        eHomWhiskerRight SSet
          (ObjectProperty.homMk (unitIsoSelf (X := X.obj)).hom :
            (d3PointedKanIhom (𝟙_ PointedSimplicialSet.{u})).obj X ⟶ X) Y := by
  change (PointedMapping.ihomAction (𝟙_ PointedSimplicialSet.{u}) X.obj Y.obj).right ≫
      eHomWhiskerLeft SSet (PointedObject.basedHom (𝟙_ PointedSimplicialSet.{u}) X.obj)
        (unitIsoSelf (X := Y.obj)).hom =
      eHomWhiskerRight SSet (unitIsoSelf (X := X.obj)).hom Y.obj
  rw [PointedEnrichment.whiskerLeft_eq, PointedEnrichment.whiskerRight_eq]
  have h := d3Closed_unit_action X.obj Y.obj
  rw [← PointedMapping.ihomAction_eq_curry_comp,
    ← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre] at h
  exact congrArg Under.Hom.right h

/-- 同じ元の単位同型を成分とする実豊穣自然変換。 -/
def d3PointedKanUnitTransformation :
    GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u}))
      (d3PointedKanIhom (𝟙_ PointedSimplicialSet.{u}))
      (EnrichedFunctor.id SSet PointedKanObject.{u}) where
  app X := eHomEquiv SSet (ObjectProperty.homMk (unitIsoSelf (X := X.obj)).hom)
  naturality X Y := ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.enriched_whiskered_square_iff SSet
    (unitIsoSelf (X := X.obj)).hom (unitIsoSelf (X := Y.obj)).hom
    ((EnrichedFunctor.id SSet PointedKanObject.{u}).map X Y)
    ((d3PointedKanIhom (𝟙_ PointedSimplicialSet.{u})).map X Y)).mp
      (d3PointedKanUnit_whiskered X Y).symm).symm

/-- coherent な自然変換の成分も、同じ元の標準単位同型そのもの。 -/
lemma d3PointedKanUnitTransformation_component (X : PointedKanObject.{u}) :
    StrictEnrichedTransformation.componentHom
      (d3PointedKanIhom (𝟙_ PointedSimplicialSet.{u}))
      (EnrichedFunctor.id SSet PointedKanObject.{u}) d3PointedKanUnitTransformation X =
        ObjectProperty.homMk (unitIsoSelf (X := X.obj)).hom := by
  change (SimplicialCategory.homEquiv' _ _).symm
    ((SSet.unitHomEquiv _) (eHomEquiv SSet
      (ObjectProperty.homMk (unitIsoSelf (X := X.obj)).hom :
        (d3PointedKanIhom (𝟙_ PointedSimplicialSet.{u})).obj X ⟶ X))) = _
  exact Equiv.symm_apply_apply _ _

/-- 単位内部 Hom の全 coherent 作用は、同じ標準単位同型で恒等作用に自然同型。 -/
def d3PointedKanUnitFunctorIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3PointedKanIhom (𝟙_ PointedSimplicialSet.{u})))
      (𝟙 PointedKanInfinity.{u}) := by
  have e := StrictEnrichedTransformation.functorIso
    (d3PointedKanIhom (𝟙_ PointedSimplicialSet.{u}))
    (EnrichedFunctor.id SSet PointedKanObject.{u}) d3PointedKanUnitTransformation (fun X ↦ by
      rw [d3PointedKanUnitTransformation_component]
      exact pointedKanObject_edge_isInvertible_of_piIsomorphism
        (ObjectProperty.homMk (unitIsoSelf (X := X.obj)).hom :
          (d3PointedKanIhom (𝟙_ PointedSimplicialSet.{u})).obj X ⟶ X) (by
            let f : (d3PointedKanIhom (𝟙_ PointedSimplicialSet.{u})).obj X ⟶ X :=
              ObjectProperty.homMk (unitIsoSelf (X := X.obj)).hom
            have : IsIso f.hom.right := by
              change IsIso (unitIsoSelf (X := X.obj)).hom.right
              infer_instance
            exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.kanPiIsomorphism_of_monoRight f.hom.right
              ((MorphismProperty.monomorphisms SSet.{u}).rlp_of_isIso _)))
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3PointedKanIhom (𝟙_ PointedSimplicialSet.{u})))
    (𝟙 (SimplicialNerve PointedKanObject.{u}))
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_id]
  exact e

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
