module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.FilteredExactness

/-!
概要：関手圏の複体に対する完全 colim を、元の複体図式の strict 余極限と比較する。
方針：次数ごとの標準余極限表示を使い、同じ余極限の普遍性で同型を作る。
規約：加群複体の通常の strict 余極限を使う。
使われ方：filtered bar の局所縮約から大域の擬同型へ移る。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits HomologicalComplex
variable (R : Type u) [CommRing R] {J : Type u} [SmallCategory J]

def dgStrictComplexColimitDegreeIso (F : J ⥤ CochainComplex (ModuleCat.{u} R) ℤ) :
    ((colim (J := J) (C := ModuleCat.{u} R)).mapHomologicalComplex (.up ℤ)).obj
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictComplexDiagram R F) ≅ (HomologicalComplex.coconeOfHasColimitEval F).pt :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by intro n m h; rfl)

def dgStrictComplexColimitIso (F : J ⥤ CochainComplex (ModuleCat.{u} R) ℤ) :
    ((colim (J := J) (C := ModuleCat.{u} R)).mapHomologicalComplex (.up ℤ)).obj
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictComplexDiagram R F) ≅ colimit F :=
  dgStrictComplexColimitDegreeIso R F ≪≫
    (HomologicalComplex.isColimitCoconeOfHasColimitEval F).coconePointUniqueUpToIso
      (colimit.isColimit F)

@[reassoc] lemma dgStrictComplexColimitIso_ι
    (F : J ⥤ CochainComplex (ModuleCat.{u} R) ℤ) (j : J) (n : ℤ) :
    colimit.ι (F ⋙ HomologicalComplex.eval (ModuleCat R) (.up ℤ) n) j ≫
      (dgStrictComplexColimitIso R F).hom.f n = (colimit.ι F j).f n := by
  have h := congrArg (fun f => f.f n)
    ((HomologicalComplex.isColimitCoconeOfHasColimitEval F).comp_coconePointUniqueUpToIso_hom
      (colimit.isColimit F) j)
  simpa only [dgStrictComplexColimitIso, Iso.trans_hom, HomologicalComplex.comp_f,
    dgStrictComplexColimitDegreeIso, HomologicalComplex.Hom.isoOfComponents_hom_f,
    Iso.refl_hom, Category.id_comp] using! h

lemma dgStrictComplexColimitIso_naturality
    {F G : J ⥤ CochainComplex (ModuleCat.{u} R) ℤ} (τ : F ⟶ G) :
    (dgStrictComplexColimitIso R F).hom ≫ colim.map τ =
      ((colim (J := J) (C := ModuleCat.{u} R)).mapHomologicalComplex (.up ℤ)).map
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictComplexDiagramMap R τ) ≫ (dgStrictComplexColimitIso R G).hom := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply colimit.hom_ext
  intro j
  change colimit.ι (F ⋙ HomologicalComplex.eval (ModuleCat R) (.up ℤ) n) j ≫
      (dgStrictComplexColimitIso R F).hom.f n ≫ (colim.map τ).f n =
    colimit.ι (F ⋙ HomologicalComplex.eval (ModuleCat R) (.up ℤ) n) j ≫
      colim.map ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictComplexDiagramMap R τ).f n) ≫ (dgStrictComplexColimitIso R G).hom.f n
  rw [dgStrictComplexColimitIso_ι_assoc R F j n]
  rw [colimit.ι_map_assoc]
  change (colimit.ι F j).f n ≫ (colim.map τ).f n =
    (τ.app j).f n ≫ (colimit.ι (G ⋙ HomologicalComplex.eval (ModuleCat R) (.up ℤ) n) j ≫
      (dgStrictComplexColimitIso R G).hom.f n)
  rw [dgStrictComplexColimitIso_ι R G j n]
  have h := congrArg (fun f => f.f n) (colimit.ι_map τ j)
  simpa only [HomologicalComplex.comp_f] using! h

lemma dgStrictFilteredColimit_quasiIso [IsFiltered J]
    {F G : J ⥤ CochainComplex (ModuleCat.{u} R) ℤ} (τ : F ⟶ G)
    (hτ : ∀ j, QuasiIso (τ.app j)) : QuasiIso (colim.map τ) := by
  letI := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgStrictComplexDiagramMap_colimit_quasiIso R τ hτ
  apply (quasiIso_iff_comp_left (dgStrictComplexColimitIso R F).hom _).mp
  rw [dgStrictComplexColimitIso_naturality]
  infer_instance

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
