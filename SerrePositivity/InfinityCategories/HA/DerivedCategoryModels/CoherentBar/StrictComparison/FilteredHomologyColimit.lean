module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.ComplexHomologyCoordinates

/-!
概要：非有界加群複体の filtered 余極限とホモロジーの標準比較。
方針：AB5 による完全 colim を隣接短複体へ適用する。
規約：有界性は仮定せず、全整数次数で比較する。
使われ方：strict augmentation の標的側のホモロジー余極限。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits DifferentialGraded HomologicalComplex
variable (R : Type u) [CommRing R] {J : Type u} [SmallCategory J]
  (F : J ⥤ Complex R) (q : ℤ)

def dgStrictComplexHomologyDiagramIso :
    F ⋙ HomologicalComplex.homologyFunctor (ModuleCat R) (.up ℤ) q ≅
      ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictComplexDiagram R F).sc' (q - 1) q (q + 1)).homology := by
  let S := (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictComplexDiagram R F).sc' (q - 1) q (q + 1)
  refine NatIso.ofComponents (fun j =>
    (F.obj j).homologyIsoSc' (q - 1) q (q + 1) (by simp) (by simp) ≪≫
      S.mapHomologyIso ((evaluation J (ModuleCat R)).obj j)) ?_
  intro j k f
  have heq : (HomologicalComplex.shortComplexFunctor' (ModuleCat R) (.up ℤ)
      (q - 1) q (q + 1)).map (F.map f) =
        S.mapNatTrans ((evaluation J (ModuleCat R)).map f) := by
    ext <;> rfl
  change HomologicalComplex.homologyMap (F.map f) q ≫
      ((F.obj k).homologyIsoSc' (q - 1) q (q + 1) (by simp) (by simp)).hom ≫ _ = _
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgComplexHomologyIsoSc_naturality, Category.assoc, heq,
    ShortComplex.homologyMap_mapNatTrans]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

variable [IsFiltered J]

def dgFilteredComplexHomologyColimitIso : (colimit F).homology q ≅
    colimit (F ⋙ HomologicalComplex.homologyFunctor (ModuleCat R) (.up ℤ) q) := by
  let T := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictComplexDiagram R F
  let S := T.sc' (q - 1) q (q + 1)
  let L := ((colim (J := J) (C := ModuleCat.{u} R)).mapHomologicalComplex (.up ℤ)).obj T
  exact (HomologicalComplex.homologyMapIso (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictComplexColimitIso R F) q).symm ≪≫
    L.homologyIsoSc' (q - 1) q (q + 1) (by simp) (by simp) ≪≫
    S.mapHomologyIso (colim (J := J) (C := ModuleCat.{u} R)) ≪≫
    (colim.mapIso (dgStrictComplexHomologyDiagramIso R F q)).symm

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
