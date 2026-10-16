module
public import SerrePositivity.HomologicalAlgebra.TensorBaseChangeNaturality
public import SerrePositivity.HomologicalAlgebra.CochainSingleMonoidal

/-! # Tensor base change and the original degree-zero comparison -/
@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex
variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)

/-- The scalar extension tensor comparison respects the original discrete tensor comparison. -/
lemma cochainTensorBaseChangeIso_single (M N : ModuleCat.{u} R) :
    (cochainTensorBaseChangeIso φ (cochainSingleZero M) (cochainSingleZero N)).hom ≫
        cochainTensorMap
          ((HomologicalComplex.singleMapHomologicalComplex
            (ModuleCat.extendScalars φ) (.up ℤ) 0).hom.app M)
          ((HomologicalComplex.singleMapHomologicalComplex
            (ModuleCat.extendScalars φ) (.up ℤ) 0).hom.app N) ≫
        (cochainSingleTensorIso ((ModuleCat.extendScalars φ).obj M)
          ((ModuleCat.extendScalars φ).obj N)).hom =
      ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).map
          (cochainSingleTensorIso M N).hom ≫
        (HomologicalComplex.singleMapHomologicalComplex
          (ModuleCat.extendScalars φ) (.up ℤ) 0).hom.app (M ⊗ N) ≫
        (CochainComplex.singleFunctor (ModuleCat S) 0).map
          (Functor.OplaxMonoidal.δ (ModuleCat.extendScalars φ) M N) := by
  let F := ModuleCat.extendScalars φ
  let ι := ιTensorObj (cochainSingleZero M) (cochainSingleZero N) 0 0 0 (by simp)
  have hi : IsIso ι := by
    have hcomp : IsIso (ι ≫ (cochainSingleTensorIso M N).hom.f 0) := by
      dsimp only [ι]
      rw [cochainSingleTensorIso_ι]
      infer_instance
    exact IsIso.of_isIso_comp_right ι ((cochainSingleTensorIso M N).hom.f 0)
  apply HomologicalComplex.to_single_hom_ext
  apply (cancel_epi (F.map ι)).mp
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
  change F.map ι ≫ (cochainTensorBaseChangeXIso φ _ _ 0).hom ≫ _ = _
  dsimp only [ι]
  rw [map_ι_cochainTensorBaseChangeXIso_assoc, ιTensorObj_cochainTensorMap_assoc]
  erw [cochainSingleTensorIso_ι (F.obj M) (F.obj N)]
  rw [← Functor.map_comp_assoc, cochainSingleTensorIso_ι]
  simp only [HomologicalComplex.singleMapHomologicalComplex_hom_app_self, Category.assoc]
  erw [HomologicalComplex.single_map_f_self]
  dsimp only [F]
  simp only [Functor.map_comp, Category.assoc]
  simp only [tensorHom_comp_tensorHom_assoc, Category.assoc, Iso.inv_hom_id_assoc]
  have hF : (ModuleCat.extendScalars φ).map (singleObjXSelf (.up ℤ) 0 (M ⊗ N)).inv ≫
      (ModuleCat.extendScalars φ).map (singleObjXSelf (.up ℤ) 0 (M ⊗ N)).hom = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id]
  rw [← Category.assoc
    ((ModuleCat.extendScalars φ).map (singleObjXSelf (.up ℤ) 0 (M ⊗ N)).inv)
    ((ModuleCat.extendScalars φ).map (singleObjXSelf (.up ℤ) 0 (M ⊗ N)).hom),
    hF, Category.id_comp]
  exact Functor.OplaxMonoidal.δ_natural_assoc (ModuleCat.extendScalars φ)
    (singleObjXSelf (.up ℤ) 0 M).hom (singleObjXSelf (.up ℤ) 0 N).hom _

end SerrePositivity
