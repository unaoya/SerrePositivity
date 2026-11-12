module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.FilteredHomologyColimit

/-!
概要：filtered ホモロジー余極限同型は元の余極限の全ての脚と可換。
方針：評価から colim への自然変換に短複体のホモロジー比較を適用する。
規約：非有界の全整数次数を扱う。
使われ方：strict augmentation が誘導する射を標準同型へ合わせる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits DifferentialGraded HomologicalComplex
variable (R : Type u) [CommRing R] {J : Type u} [SmallCategory J]

def dgFilteredEvaluationLeg (j : J) :
    (evaluation J (ModuleCat.{u} R)).obj j ⟶ colim (J := J) (C := ModuleCat.{u} R) where
  app F := colimit.ι F j
  naturality {F H} α := (colimit.ι_map α j).symm

variable (F : J ⥤ Complex R)

def dgFilteredComplexLeg (j : J) : F.obj j ⟶
    ((colim (J := J) (C := ModuleCat.{u} R)).mapHomologicalComplex (.up ℤ)).obj
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictComplexDiagram R F) :=
  CochainComplex.ofHom (fun q => colimit.ι ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictComplexDiagram R F).X q) j)
    (fun q => colimit.ι_map ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictComplexDiagram R F).d q (q + 1)) j)

lemma dgFilteredComplexLeg_comparison (j : J) :
    dgFilteredComplexLeg R F j ≫ (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictComplexColimitIso R F).hom = colimit.ι F j := by
  apply HomologicalComplex.Hom.ext
  funext q
  exact _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictComplexColimitIso_ι R F j q

variable [IsFiltered J]

@[reassoc]
lemma dgFilteredComplexHomologyColimitIso_leg (j : J) (q : ℤ) :
    HomologicalComplex.homologyMap (colimit.ι F j) q ≫
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgFilteredComplexHomologyColimitIso R F q).hom =
    colimit.ι (F ⋙ HomologicalComplex.homologyFunctor (ModuleCat R) (.up ℤ) q) j := by
  let T := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictComplexDiagram R F
  let S := T.sc' (q - 1) q (q + 1)
  let L := ((colim (J := J) (C := ModuleCat.{u} R)).mapHomologicalComplex (.up ℤ)).obj T
  have heq : (HomologicalComplex.shortComplexFunctor' (ModuleCat R) (.up ℤ)
      (q - 1) q (q + 1)).map (dgFilteredComplexLeg R F j) =
        S.mapNatTrans (dgFilteredEvaluationLeg R j) := by
    ext <;> rfl
  have h : HomologicalComplex.homologyMap (dgFilteredComplexLeg R F j) q ≫
      (L.homologyIsoSc' (q - 1) q (q + 1) (by simp) (by simp)).hom ≫
      (S.mapHomologyIso (colim (J := J) (C := ModuleCat.{u} R))).hom =
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictComplexHomologyDiagramIso R F q).hom.app j ≫ colimit.ι S.homology j := by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgComplexHomologyIsoSc_naturality, Category.assoc, heq,
      ShortComplex.homologyMap_mapNatTrans]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rfl
  rw [← dgFilteredComplexLeg_comparison R F j, HomologicalComplex.homologyMap_comp]
  dsimp only [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgFilteredComplexHomologyColimitIso, Iso.trans_hom, Iso.symm_hom]
  change (HomologicalComplex.homologyMap (dgFilteredComplexLeg R F j) q ≫
    (HomologicalComplex.homologyMapIso (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictComplexColimitIso R F) q).hom) ≫ _ = _
  rw [Category.assoc, Iso.hom_inv_id_assoc]
  change (HomologicalComplex.homologyMap (dgFilteredComplexLeg R F j) q ≫
    (L.homologyIsoSc' (q - 1) q (q + 1) (by simp) (by simp)).hom ≫
    (S.mapHomologyIso (colim (J := J) (C := ModuleCat.{u} R))).hom) ≫
      (colim.mapIso (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictComplexHomologyDiagramIso R F q)).inv = _
  rw [h, Category.assoc]
  change (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictComplexHomologyDiagramIso R F q).hom.app j ≫
    (colimit.ι S.homology j ≫ colim.map (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictComplexHomologyDiagramIso R F q).inv) = _
  rw [colimit.ι_map]
  simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
