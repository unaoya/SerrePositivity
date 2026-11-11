module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.StrictAugmentationHomologyLegs

/-!
概要：実 bar の余核射と strict 標準増大の合成は、標的の標準余核射に等しい。
方針：零段階の実増大の比較と零次元層の全係数比較を合わせる。
規約：同じ strict 標準射が誘導するホモロジー射を用いる。
使われ方：二つの余核の普遍性による擬同型判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits DifferentialGraded SSet
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {J : Type u} [PartialOrder J] [IsFiltered J] (F : J ⥤ _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D)

lemma dgCoherentBarStrictAugmentation_homology (x : D) (q : ℤ) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyBarAugmentation R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F) x q ≫
      HomologicalComplex.homologyMap
        ((moduleEvaluation R D x).map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictColimitAugmentation R D F)) q =
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarNondegAugmentation R
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyDiagram R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F) x q)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictCoherentHomologyCocone R D F x q) := by
  let G := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F
  rw [← cancel_epi (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarZeroStageHomologyIso R D G x q).hom]
  dsimp only [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyBarAugmentation, G]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  have hz := congrArg (fun f => HomologicalComplex.homologyMap f q)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarZeroStage_augmentation R D F (colimit.cocone F) x)
  simp only [HomologicalComplex.homologyMap_comp] at hz
  change HomologicalComplex.homologyMap
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNormalizedStageInclusion R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F) x 0) q ≫
      HomologicalComplex.homologyMap ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation R D x).map
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictAugmentation R D F (colimit.cocone F))) q = _
  rw [← hz]
  change HomologicalComplex.homologyMap (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarZeroStageIso R D G x).hom q ≫ _ =
    (HomologicalComplex.homologyMap (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarZeroStageIso R D G x).hom q ≫
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarNaturalLayerHomologyIso R D G x 0 q q (by omega)).hom) ≫ _
  rw [Category.assoc, ← _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictZeroLayer_homologyAugmentation]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
