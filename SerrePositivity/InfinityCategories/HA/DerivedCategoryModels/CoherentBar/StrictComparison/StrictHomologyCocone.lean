module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.StrictHomologyColimit

/-!
概要：strict dg 余極限のホモロジーは coherent ホモロジー図式の余極限余錐を持つ。
方針：検証済みの標準ホモロジー同型で選ばれた余極限余錐を輸送する。
規約：全ての脚は元の dg 余錐のホモロジー射と一致する。
使われ方：strict bar 増大の標的における余核の普遍性。
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

def dgStrictCoherentHomologyCocone (x : D) (q : ℤ) :
    Cocone (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyDiagram R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F) x q) :=
  (colimit.cocone _).extend (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictCoherentHomologyColimitIso R D F x q).inv

def dgStrictCoherentHomologyCoconeIsColimit (x : D) (q : ℤ) :
    IsColimit (dgStrictCoherentHomologyCocone R D F x q) :=
  IsColimit.ofIsoColimit (colimit.isColimit _)
    (Cocone.ext (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictCoherentHomologyColimitIso R D F x q).symm (fun j => rfl))

lemma dgStrictCoherentHomologyCocone_leg (x : D) (q : ℤ) (j : J) :
    (dgStrictCoherentHomologyCocone R D F x q).ι.app j =
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyDiagramObjIso R D (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarStrictDiagram R D F) x q j).hom ≫
      HomologicalComplex.homologyMap ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation R D x).map (colimit.ι F j)) q := by
  rw [← cancel_mono (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictCoherentHomologyColimitIso R D F x q).hom]
  change (colimit.ι _ j ≫ (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictCoherentHomologyColimitIso R D F x q).inv) ≫ _ = _
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictCoherentHomologyColimitIso_leg R D F x q j).symm

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
