module
public import SerrePositivity.HomologicalAlgebra.TensorSingleNaturality
public import SerrePositivity.HomologicalAlgebra.CochainTensorTriple
public import SerrePositivity.HomologicalAlgebra.CochainTensorHomotopy

/-! # Canonical tensor comparisons for actual discrete cochain complexes -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex
open scoped TensorProduct
variable {R : Type u} [CommRing R]

/-- Tensoring two actual degree-zero complexes recovers their ordinary tensor in degree zero. -/
def cochainSingleTensorIso (M N : ModuleCat.{u} R) :
    cochainTensor (cochainSingleZero M) (cochainSingleZero N) ≅
      cochainSingleZero (M ⊗ N) :=
  cochainTensorSingleLeftIso M (cochainSingleZero N) ≪≫
    (HomologicalComplex.singleMapHomologicalComplex (tensorLeft M) (.up ℤ) 0).app N

/-- The canonical comparison uses the ordinary tensor on the only nonzero bidegree. -/
@[reassoc] lemma cochainSingleTensorIso_ι (M N : ModuleCat.{u} R) :
    ιTensorObj (cochainSingleZero M) (cochainSingleZero N) 0 0 0 (by simp) ≫
      (cochainSingleTensorIso M N).hom.f 0 =
    ((singleObjXSelf (.up ℤ) 0 M).hom ⊗ₘ (singleObjXSelf (.up ℤ) 0 N).hom) ≫
      (singleObjXSelf (.up ℤ) 0 (M ⊗ N)).inv := by
  change ιTensorObj (cochainSingleZero M) (cochainSingleZero N) 0 0 0 (by simp) ≫
    tensorSingleLeftDesc M (cochainSingleZero N) 0 ≫
      ((HomologicalComplex.singleMapHomologicalComplex (tensorLeft M) (.up ℤ) 0).hom.app N).f 0 = _
  rw [ι_tensorSingleLeftDesc_assoc,
    HomologicalComplex.singleMapHomologicalComplex_hom_app_self]
  rw [tensorHom_def]
  rfl

/-- The degree-zero comparison sends a homogeneous pure tensor to the ordinary pure tensor. -/
lemma cochainSingleTensorIso_hom_apply_ι (M N : ModuleCat.{u} R)
    (x : (cochainSingleZero M).X 0) (y : (cochainSingleZero N).X 0) :
    (cochainSingleTensorIso M N).hom.f 0
        (ιTensorObj (cochainSingleZero M) (cochainSingleZero N) 0 0 0 (by simp)
          (x ⊗ₜ[R] y)) =
      (singleObjXSelf (.up ℤ) 0 (M ⊗ N)).inv
        ((singleObjXSelf (.up ℤ) 0 M).hom x ⊗ₜ[R]
          (singleObjXSelf (.up ℤ) 0 N).hom y) := by
  exact congrArg (fun h => h (x ⊗ₜ[R] y)) (cochainSingleTensorIso_ι M N)

/-- The comparison is natural in the right module. -/
lemma cochainSingleTensorIso_naturality_right
    (M : ModuleCat.{u} R) {N N' : ModuleCat.{u} R} (g : N ⟶ N') :
    cochainTensorMap (𝟙 (cochainSingleZero M))
        ((CochainComplex.singleFunctor (ModuleCat R) 0).map g) ≫
      (cochainSingleTensorIso M N').hom =
    (cochainSingleTensorIso M N).hom ≫
      (CochainComplex.singleFunctor (ModuleCat R) 0).map ((tensorLeft M).map g) := by
  simp only [cochainSingleTensorIso, Iso.trans_hom, Category.assoc]
  rw [← Category.assoc, cochainTensorSingleLeftIso_naturality, Category.assoc]
  have hn := (HomologicalComplex.singleMapHomologicalComplex
    (tensorLeft M) (.up ℤ) 0).hom.naturality g
  exact congrArg ((cochainTensorSingleLeftIso M (cochainSingleZero N)).hom ≫ ·) hn

/-- The comparison is natural in the left module. -/
lemma cochainSingleTensorIso_naturality_left
    {M M' : ModuleCat.{u} R} (f : M ⟶ M') (N : ModuleCat.{u} R) :
    cochainTensorMap ((CochainComplex.singleFunctor (ModuleCat R) 0).map f)
        (𝟙 (cochainSingleZero N)) ≫ (cochainSingleTensorIso M' N).hom =
    (cochainSingleTensorIso M N).hom ≫
      (CochainComplex.singleFunctor (ModuleCat R) 0).map
        (((tensoringLeft (ModuleCat.{u} R)).map f).app N) := by
  simp only [cochainSingleTensorIso, Iso.trans_hom, Category.assoc]
  rw [← Category.assoc, cochainTensorSingleLeftIso_module_naturality, Category.assoc]
  rw [HomologicalComplex.natTransMapHomologicalComplex_app_single_obj]
  simp only [Iso.app_hom, Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]

/-- The signed cochain symmetry agrees with ordinary symmetry under the discrete comparison. -/
lemma cochainSingleTensorIso_symmetry (M N : ModuleCat.{u} R) :
    (cochainTensorSymmetry (cochainSingleZero M) (cochainSingleZero N)).hom ≫
      (cochainSingleTensorIso N M).hom =
    (cochainSingleTensorIso M N).hom ≫
      (CochainComplex.singleFunctor (ModuleCat R) 0).map (β_ M N).hom := by
  apply HomologicalComplex.to_single_hom_ext
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j hij
  by_cases hi : i = 0
  · subst i
    have hj : j = 0 := by dsimp at hij; omega
    subst j
    simp only [HomologicalComplex.comp_f]
    rw [ιTensorObj_cochainTensorSymmetry_assoc]
    simp only [mul_zero, Int.negOnePow_zero, one_smul, Category.assoc]
    rw [cochainSingleTensorIso_ι, cochainSingleTensorIso_ι_assoc]
    rw [HomologicalComplex.single_map_f_self]
    simp only [Iso.inv_hom_id_assoc]
    exact (BraidedCategory.braiding_naturality_assoc
      (singleObjXSelf (.up ℤ) 0 M).hom (singleObjXSelf (.up ℤ) 0 N).hom _).symm
  · have hz := isZero_single_obj_X (.up ℤ) 0 M i hi
    exact ((tensorRight ((cochainSingleZero N).X j)).map_isZero hz).eq_of_src _ _

set_option maxHeartbeats 600000 in
-- The triple totalization has dependent degree indices and three nested tensor comparisons.
/-- The discrete tensor comparison intertwines the actual cochain associator
with the ordinary module associator. -/
lemma cochainSingleTensorIso_associator (M N P : ModuleCat.{u} R) :
    cochainTensorMap (cochainSingleTensorIso M N).hom (𝟙 (cochainSingleZero P)) ≫
        (cochainSingleTensorIso (M ⊗ N) P).hom ≫
        (CochainComplex.singleFunctor (ModuleCat R) 0).map (α_ M N P).hom =
      (cochainTensorAssociator (cochainSingleZero M) (cochainSingleZero N)
          (cochainSingleZero P)).hom ≫
        cochainTensorMap (𝟙 (cochainSingleZero M)) (cochainSingleTensorIso N P).hom ≫
        (cochainSingleTensorIso M (N ⊗ P)).hom := by
  apply HomologicalComplex.to_single_hom_ext
  apply cochainTensorTriple_hom_ext
    (cochainSingleZero M) (cochainSingleZero N) (cochainSingleZero P) 0
  intro i j k hijk
  by_cases hi : i = 0
  · subst i
    by_cases hj : j = 0
    · subst j
      have hk : k = 0 := by omega
      subst k
      apply ModuleCat.hom_ext
      apply TensorProduct.ext_threefold
      intro x y z
      change ((CochainComplex.singleFunctor (ModuleCat R) 0).map (α_ M N P).hom).f 0
          ((cochainSingleTensorIso (M ⊗ N) P).hom.f 0
            ((cochainTensorMap (cochainSingleTensorIso M N).hom
              (𝟙 (cochainSingleZero P))).f 0
              (cochainTensorTripleι (cochainSingleZero M) (cochainSingleZero N)
                (cochainSingleZero P) 0 0 0 0 hijk ((x ⊗ₜ[R] y) ⊗ₜ[R] z)))) =
        (cochainSingleTensorIso M (N ⊗ P)).hom.f 0
          ((cochainTensorMap (𝟙 (cochainSingleZero M))
            (cochainSingleTensorIso N P).hom).f 0
            ((cochainTensorAssociator (cochainSingleZero M) (cochainSingleZero N)
              (cochainSingleZero P)).hom.f 0
              (cochainTensorTripleι (cochainSingleZero M) (cochainSingleZero N)
                (cochainSingleZero P) 0 0 0 0 hijk ((x ⊗ₜ[R] y) ⊗ₜ[R] z))))
      rw [cochainTensorTripleι_apply]
      rw [cochainTensorMap_apply_ι]
      erw [cochainSingleTensorIso_hom_apply_ι M N x y]
      erw [cochainSingleTensorIso_hom_apply_ι (M ⊗ N) P]
      rw [cochainTensorAssociator_hom_apply_ι]
      rw [cochainTensorMap_apply_ι]
      erw [cochainSingleTensorIso_hom_apply_ι N P y z]
      erw [cochainSingleTensorIso_hom_apply_ι M (N ⊗ P)]
      simp only [HomologicalComplex.id_f, ModuleCat.id_apply]
      erw [HomologicalComplex.single_map_f_self]
      simp only [ModuleCat.comp_apply, Iso.inv_hom_id_apply,
        ModuleCat.MonoidalCategory.associator_hom_apply]
    · have hz := isZero_single_obj_X (.up ℤ) 0 N j hj
      exact ((tensorRight ((cochainSingleZero P).X k)).map_isZero
        ((tensorLeft ((cochainSingleZero M).X 0)).map_isZero hz)).eq_of_src _ _
  · have hz := isZero_single_obj_X (.up ℤ) 0 M i hi
    exact ((tensorRight ((cochainSingleZero P).X k)).map_isZero
      ((tensorRight ((cochainSingleZero N).X j)).map_isZero hz)).eq_of_src _ _

/-- The discrete tensor comparison preserves the standard left unit comparison. -/
lemma cochainSingleTensorIso_leftUnitor (M : ModuleCat.{u} R) :
    (cochainSingleTensorIso (ModuleCat.of R R) M).hom ≫
        (CochainComplex.singleFunctor (ModuleCat R) 0).map (λ_ M).hom =
      (cochainTensorLeftUnitor (cochainSingleZero M)).hom := by
  apply (cancel_epi (cochainTensorLeftUnitor (cochainSingleZero M)).inv).mp
  rw [Iso.inv_hom_id]
  apply HomologicalComplex.to_single_hom_ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hl : (cochainTensorLeftUnitor (cochainSingleZero M)).inv.f 0 x =
      ιTensorObj (cochainSingleZero (ModuleCat.of R R)) (cochainSingleZero M) 0 0 0 (by simp)
        ((singleObjXSelf (.up ℤ) 0 (ModuleCat.of R R)).inv (1 : R) ⊗ₜ[R] x) := by
    change (HomologicalComplex.leftUnitor' (cochainSingleZero M)).inv 0 x = _
    rw [HomologicalComplex.leftUnitor'_inv]
    rfl
  change ((CochainComplex.singleFunctor (ModuleCat R) 0).map (λ_ M).hom).f 0
    ((cochainSingleTensorIso (ModuleCat.of R R) M).hom.f 0
      ((cochainTensorLeftUnitor (cochainSingleZero M)).inv.f 0 x)) = x
  rw [hl, cochainSingleTensorIso_hom_apply_ι]
  erw [HomologicalComplex.single_map_f_self]
  simp only [ModuleCat.comp_apply, Iso.inv_hom_id_apply]
  change (singleObjXSelf (.up ℤ) 0 M).inv ((λ_ M).hom
    ((singleObjXSelf (.up ℤ) 0 (ModuleCat.of R R ⊗ M)).hom
      ((singleObjXSelf (.up ℤ) 0 (ModuleCat.of R R ⊗ M)).inv
        ((1 : R) ⊗ₜ[R] (singleObjXSelf (.up ℤ) 0 M).hom x)))) = x
  simp only [Iso.inv_hom_id_apply]
  erw [ModuleCat.MonoidalCategory.leftUnitor_hom_apply]
  simp only [one_smul]
  rfl

/-- The discrete tensor comparison preserves the standard right unit comparison. -/
lemma cochainSingleTensorIso_rightUnitor (M : ModuleCat.{u} R) :
    (cochainSingleTensorIso M (ModuleCat.of R R)).hom ≫
        (CochainComplex.singleFunctor (ModuleCat R) 0).map (ρ_ M).hom =
      (cochainTensorRightUnitor (cochainSingleZero M)).hom := by
  apply (cancel_epi (cochainTensorRightUnitor (cochainSingleZero M)).inv).mp
  rw [Iso.inv_hom_id]
  apply HomologicalComplex.to_single_hom_ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hr : (cochainTensorRightUnitor (cochainSingleZero M)).inv.f 0 x =
      ιTensorObj (cochainSingleZero M) (cochainSingleZero (ModuleCat.of R R)) 0 0 0 (by simp)
        (x ⊗ₜ[R] (singleObjXSelf (.up ℤ) 0 (ModuleCat.of R R)).inv (1 : R)) := by
    change (HomologicalComplex.rightUnitor' (cochainSingleZero M)).inv 0 x = _
    rw [HomologicalComplex.rightUnitor'_inv]
    rfl
  change ((CochainComplex.singleFunctor (ModuleCat R) 0).map (ρ_ M).hom).f 0
    ((cochainSingleTensorIso M (ModuleCat.of R R)).hom.f 0
      ((cochainTensorRightUnitor (cochainSingleZero M)).inv.f 0 x)) = x
  rw [hr, cochainSingleTensorIso_hom_apply_ι]
  erw [HomologicalComplex.single_map_f_self]
  simp only [ModuleCat.comp_apply, Iso.inv_hom_id_apply]
  change (singleObjXSelf (.up ℤ) 0 M).inv ((ρ_ M).hom
    ((singleObjXSelf (.up ℤ) 0 (M ⊗ ModuleCat.of R R)).hom
      ((singleObjXSelf (.up ℤ) 0 (M ⊗ ModuleCat.of R R)).inv
        ((singleObjXSelf (.up ℤ) 0 M).hom x ⊗ₜ[R] (1 : R))))) = x
  simp only [Iso.inv_hom_id_apply]
  erw [ModuleCat.MonoidalCategory.rightUnitor_hom_apply]
  simp only [one_smul]
  rfl

end SerrePositivity
