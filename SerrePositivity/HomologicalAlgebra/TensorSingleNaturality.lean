module
public import SerrePositivity.HomologicalAlgebra.CochainTensorSingle
public import SerrePositivity.HomologicalAlgebra.TensorBaseChangeNaturality
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors

/-! # Naturality of tensoring with a degree-zero module -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex
variable {R : Type u} [CommRing R]

/-- The total-to-pointwise tensor comparison is natural in the complex. -/
lemma cochainTensorSingleLeftIso_naturality (V : ModuleCat.{u} R)
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (f : P ⟶ Q) :
    cochainTensorMap (𝟙 (cochainSingleZero V)) f ≫ (cochainTensorSingleLeftIso V Q).hom =
      (cochainTensorSingleLeftIso V P).hom ≫
        ((tensorLeft V).mapHomologicalComplex (.up ℤ)).map f := by
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j hij
  by_cases hi : i = 0
  · subst i
    have hj : j = n := by dsimp at hij; omega
    subst j
    change ιTensorObj (cochainSingleZero V) P 0 n n (zero_add n) ≫
        ((cochainTensorMap (𝟙 (cochainSingleZero V)) f).f n ≫ tensorSingleLeftDesc V Q n) =
      ιTensorObj (cochainSingleZero V) P 0 n n (zero_add n) ≫
        (tensorSingleLeftDesc V P n ≫ (V ◁ f.f n))
    rw [cochainTensorMap_homogeneous_assoc, ι_tensorSingleLeftDesc,
      ι_tensorSingleLeftDesc_assoc]
    simp only [HomologicalComplex.id_f, id_tensorHom]
    exact whisker_exchange (singleObjXSelf (.up ℤ) 0 V).hom (f.f n)
  · have hz := isZero_single_obj_X (.up ℤ) 0 V i hi
    exact ((tensorRight (P.X j)).map_isZero hz).eq_of_src _ _

/-- The total-to-pointwise comparison is also natural in the degree-zero module. -/
lemma cochainTensorSingleLeftIso_module_naturality {V W : ModuleCat.{u} R} (f : V ⟶ W)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    cochainTensorMap ((CochainComplex.singleFunctor (ModuleCat R) 0).map f) (𝟙 P) ≫
        (cochainTensorSingleLeftIso W P).hom =
      (cochainTensorSingleLeftIso V P).hom ≫
        (NatTrans.mapHomologicalComplex ((tensoringLeft (ModuleCat R)).map f) (.up ℤ)).app P := by
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j hij
  by_cases hi : i = 0
  · subst i
    have hj : j = n := by dsimp at hij; omega
    subst j
    change ιTensorObj (cochainSingleZero V) P 0 n n (zero_add n) ≫
        ((cochainTensorMap ((CochainComplex.singleFunctor (ModuleCat R) 0).map f)
          (𝟙 P)).f n ≫ tensorSingleLeftDesc W P n) =
      ιTensorObj (cochainSingleZero V) P 0 n n (zero_add n) ≫
        (tensorSingleLeftDesc V P n ≫ (f ▷ P.X n))
    rw [cochainTensorMap_homogeneous_assoc, ι_tensorSingleLeftDesc,
      ι_tensorSingleLeftDesc_assoc]
    simp only [HomologicalComplex.id_f, tensorHom_id, ← comp_whiskerRight]
    have hs : ((CochainComplex.singleFunctor (ModuleCat R) 0).map f).f 0 ≫
        (singleObjXSelf (.up ℤ) 0 W).hom = (singleObjXSelf (.up ℤ) 0 V).hom ≫ f := by
      rw [HomologicalComplex.single_map_f_self]
      simp
    exact congrArg (fun g => g ▷ P.X n) hs
  · have hz := isZero_single_obj_X (.up ℤ) 0 V i hi
    exact ((tensorRight (P.X j)).map_isZero hz).eq_of_src _ _

end SerrePositivity
