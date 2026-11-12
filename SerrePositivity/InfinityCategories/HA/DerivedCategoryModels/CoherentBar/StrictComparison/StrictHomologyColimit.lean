module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.StrictHomologyDiagram
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.FilteredHomologyColimitLegs
public import SerrePositivity.DifferentialGraded.Module.ActionLimits

/-!
概要：strict dg 余極限のホモロジーを coherent ホモロジー図式の余極限へ同定する。
方針：評価の余極限保存、AB5、strict/coherent の自然同型を合成する。
規約：全ての元の余極限の脚と可換な標準比較を使う。
使われ方：strict bar 標準射のホモロジー余核との照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits DifferentialGraded SSet
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {J : Type u} [SmallCategory J] [IsFiltered J] (F : J ⥤ _root_.SerrePositivity.DifferentialGraded.ModuleCategory R D)

def dgStrictCoherentHomologyColimitIso (x : D) (q : ℤ) :
    ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation R D x).obj (colimit F)).homology q ≅
      colimit (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyDiagram R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F) x q) :=
  HomologicalComplex.homologyMapIso (_root_.SerrePositivity.DifferentialGraded.moduleEvaluationColimitIso R D F x) q ≪≫
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgFilteredComplexHomologyColimitIso R (F ⋙ moduleEvaluation R D x) q ≪≫
    (colim.mapIso (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictHomologyDiagramIso R D F x q)).symm

@[reassoc]
lemma dgStrictCoherentHomologyColimitIso_leg (x : D) (q : ℤ) (j : J) :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyDiagramObjIso R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F) x q j).hom ≫
      HomologicalComplex.homologyMap ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation R D x).map (colimit.ι F j)) q ≫
        (dgStrictCoherentHomologyColimitIso R D F x q).hom =
      colimit.ι (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyDiagram R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F) x q) j := by
  let e := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictHomologyDiagramIso R D F x q
  dsimp only [dgStrictCoherentHomologyColimitIso, Iso.trans_hom, Iso.symm_hom]
  change e.hom.app j ≫ HomologicalComplex.homologyMap
    ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation R D x).map (colimit.ι F j)) q ≫
      HomologicalComplex.homologyMap (_root_.SerrePositivity.DifferentialGraded.moduleEvaluationColimitIso R D F x).hom q ≫ _ = _
  rw [← Category.assoc (HomologicalComplex.homologyMap _ _),
    ← HomologicalComplex.homologyMap_comp, _root_.SerrePositivity.DifferentialGraded.moduleEvaluationColimitIso_ι_hom,
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgFilteredComplexHomologyColimitIso_leg_assoc]
  change e.hom.app j ≫ (colimit.ι _ j ≫ colim.map e.inv) = _
  rw [colimit.ι_map]
  simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
