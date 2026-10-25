module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.StrictHomologyDiagram
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.FilteredHomologyColimitLegs
public import SerrePositivity.DifferentialGraded.Module.Colimits

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {J : Type u} [SmallCategory J] [IsFiltered J] (F : J ⥤ ModuleCategory R D)

def dgStrictCoherentHomologyColimitIso (x : D) (q : ℤ) :
    ((moduleEvaluation R D x).obj (colimit F)).homology q ≅
      colimit (dgCoherentBarHomologyDiagram R D (dgCoherentBarStrictDiagram R D F) x q) :=
  HomologicalComplex.homologyMapIso (moduleEvaluationColimitIso R D F x) q ≪≫
    dgFilteredComplexHomologyColimitIso R (F ⋙ moduleEvaluation R D x) q ≪≫
    (colim.mapIso (dgCoherentBarStrictHomologyDiagramIso R D F x q)).symm

@[reassoc]
lemma dgStrictCoherentHomologyColimitIso_leg (x : D) (q : ℤ) (j : J) :
    (dgCoherentBarHomologyDiagramObjIso R D (dgCoherentBarStrictDiagram R D F) x q j).hom ≫
      HomologicalComplex.homologyMap ((moduleEvaluation R D x).map (colimit.ι F j)) q ≫
        (dgStrictCoherentHomologyColimitIso R D F x q).hom =
      colimit.ι (dgCoherentBarHomologyDiagram R D (dgCoherentBarStrictDiagram R D F) x q) j := by
  let e := dgCoherentBarStrictHomologyDiagramIso R D F x q
  dsimp only [dgStrictCoherentHomologyColimitIso, Iso.trans_hom, Iso.symm_hom]
  change e.hom.app j ≫ HomologicalComplex.homologyMap
    ((moduleEvaluation R D x).map (colimit.ι F j)) q ≫
      HomologicalComplex.homologyMap (moduleEvaluationColimitIso R D F x).hom q ≫ _ = _
  rw [← Category.assoc (HomologicalComplex.homologyMap _ _),
    ← HomologicalComplex.homologyMap_comp, moduleEvaluationColimitIso_ι_hom,
    dgFilteredComplexHomologyColimitIso_leg_assoc]
  change e.hom.app j ≫ (colimit.ι _ j ≫ colim.map e.inv) = _
  rw [colimit.ι_map]
  simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]

end SerrePositivity.InfinityCategories
