module
public import SerrePositivity.HomologicalAlgebra.AlgebraKoszulBounds
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.TowerUnit

/-! # Canonical augmentation of coefficient-algebra dual Koszul colimits -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open DerivedCompletion
variable {R C : Type u} [CommRing R] [CommRing C] [Algebra R C]
variable {e : ℕ} (z : Fin e → R)

/-- Dualize the actual standard inclusion, with no regularity assumptions. -/
def algebraKoszulDualAugmentation : algebraKoszulDualFunctor (C := C) z ⟶
    algebraKoszulDualFunctor (C := C) (Fin.elim0 : Fin 0 → R) :=
  algebraLinearYonedaMap (restrictionMap (koszulComplexInclusion R z) embUp)

/-- The actual power transitions commute strictly with the dual augmentation. -/
lemma algebraKoszulDualAugmentation_power_transition (n : ℕ) :
    algebraKoszulDualPowerTransition (C := C) z n ≫
        algebraKoszulDualAugmentation (C := C) (fun j => z j ^ (n + 1)) =
      algebraKoszulDualAugmentation (C := C) (fun j => z j ^ n) := by
  change algebraLinearYonedaMap (C := C)
      (restrictionMap (powerKoszulTransition R z n) embUp) ≫
      algebraLinearYonedaMap (C := C)
        (restrictionMap (koszulComplexInclusion R (fun j => z j ^ (n + 1))) embUp) = _
  rw [← algebraLinearYonedaMap_comp, ← restrictionMap_comp, powerKoszulInclusion_compatible]
  rfl

/-- The standard augmentations form an actual cocone of complexes of coefficient functors. -/
def algebraKoszulDualAugmentationCocone :
    Cocone (algebraKoszulDualFunctorComplexDiagram (C := C) z) where
  pt := functorCochainComplex
    (algebraKoszulDualFunctor (C := C) (Fin.elim0 : Fin 0 → R))
  ι := NatTrans.ofSequence (fun n =>
    (functorCochainComplexFunctor (ModuleCat.{u} C) (ModuleCat.{u} C)).map
      (algebraKoszulDualAugmentation (C := C) (fun j => z j ^ n))) (by
        intro n
        simp only [algebraKoszulDualFunctorComplexDiagram, algebraKoszulDualPowerDiagram,
          Functor.comp_map, Functor.ofSequence_map_homOfLE_succ,
          Functor.const_obj_map]
        rw [← Functor.map_comp, algebraKoszulDualAugmentation_power_transition]
        exact (Category.comp_id _).symm)

/-- The canonical augmentation out of the actual complex colimit. -/
def algebraKoszulDualColimitAugmentation :
    algebraKoszulDualColimitComplex (C := C) z ⟶
      functorCochainComplex
        (algebraKoszulDualFunctor (C := C) (Fin.elim0 : Fin 0 → R)) :=
  colimit.desc _ (algebraKoszulDualAugmentationCocone (C := C) z)

/-- The augmentation is natural in all actual C-module coefficients. -/
def algebraKoszulDualColimitAugmentationNatTrans :
    algebraKoszulDualColimitFunctor (C := C) z ⟶
      algebraKoszulDualFunctor (C := C) (Fin.elim0 : Fin 0 → R) :=
  complexOfFunctorsToFunctorToComplex.map (algebraKoszulDualColimitAugmentation (C := C) z)

/-- The empty dual in degree zero is evaluation of an R-linear map at one, C-linearly. -/
def algebraKoszulDualEmptyZeroEquiv (M : ModuleCat.{u} C) :
    (((algebraKoszulDualFunctor (C := C) (Fin.elim0 : Fin 0 → R)).obj M).X 0) ≃ₗ[C] M := by
  change (ModuleCat.of R R ⟶ (ModuleCat.restrictScalars (algebraMap R C)).obj M) ≃ₗ[C] M
  exact ModuleCat.homLinearEquiv.trans
    (LinearMap.ringLmapEquivSelf R C ((ModuleCat.restrictScalars (algebraMap R C)).obj M))

/-- The empty dual complex is canonically the actual coefficient module in degree zero. -/
def algebraKoszulDualEmptyIso (M : ModuleCat.{u} C) :
    (algebraKoszulDualFunctor (C := C) (Fin.elim0 : Fin 0 → R)).obj M ≅
      (CochainComplex.single₀ (ModuleCat.{u} C)).obj M :=
  Hom.isoOfComponents (fun i => match i with
    | 0 => (algebraKoszulDualEmptyZeroEquiv (R := R) (C := C) M).toModuleIso
    | n + 1 => (algebraKoszulDual_isZero_X (C := C)
        (Fin.elim0 : Fin 0 → R) M (n + 1) (by omega)).iso
      (isZero_single_obj_X (.up ℕ) 0 M (n + 1) (by omega))) (by
        intro i j hij
        have hj : j ≠ 0 := by change i + 1 = j at hij; omega
        exact (isZero_single_obj_X (.up ℕ) 0 M j hj).eq_of_tgt _ _)

/-- The identification with coefficients is natural in every C-linear coefficient map. -/
def algebraKoszulDualEmptyNatIso :
    algebraKoszulDualFunctor (C := C) (Fin.elim0 : Fin 0 → R) ≅
      CochainComplex.single₀ (ModuleCat.{u} C) :=
  NatIso.ofComponents (algebraKoszulDualEmptyIso (R := R) (C := C)) (by
    intro M N f
    apply HomologicalComplex.Hom.ext
    funext i
    cases i with
    | zero =>
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro g
      rfl
    | succ i =>
      exact (isZero_single_obj_X (.up ℕ) 0 N (i + 1) (by omega)).eq_of_tgt _ _)

/-- The canonical colimit augmentation has the actual coefficient module as its target. -/
def algebraKoszulDualColimitToSingle :
    algebraKoszulDualColimitFunctor (C := C) z ⟶ CochainComplex.single₀ (ModuleCat.{u} C) :=
  algebraKoszulDualColimitAugmentationNatTrans (C := C) z ≫
    (algebraKoszulDualEmptyNatIso (R := R) (C := C)).hom

/-- Extension of degree-zero coefficient complexes is the integer degree-zero functor. -/
def nonnegativeSingleExtendNatIso :
    CochainComplex.single₀ (ModuleCat.{u} C) ⋙
        nonnegativeCochainEmbedding.extendFunctor (ModuleCat.{u} C) ≅
      CochainComplex.singleFunctor (ModuleCat.{u} C) 0 :=
  NatIso.ofComponents (fun M => extendSingleIso nonnegativeCochainEmbedding M 0 0 rfl) (by
    intro M N f
    apply HomologicalComplex.to_single_hom_ext
    simp only [Functor.comp_map, comp_f, ComplexShape.Embedding.extendFunctor_map,
      extendMap_f _ _ (show nonnegativeCochainEmbedding.f 0 = 0 from rfl),
      CochainComplex.single₀_map_f_zero]
    rw [extendSingleIso_hom_f nonnegativeCochainEmbedding N 0 0 rfl,
      extendSingleIso_hom_f nonnegativeCochainEmbedding M 0 0 rfl]
    simp [CochainComplex.singleFunctor, single_map_f_self])

/-- Canonical augmentation from the integer colimit model to the actual coefficient complex. -/
def algebraKoszulDualIntegerToSingle :
    algebraKoszulDualIntegerColimitFunctor (C := C) z ⟶
      CochainComplex.singleFunctor (ModuleCat.{u} C) 0 :=
  Functor.whiskerRight (algebraKoszulDualColimitToSingle (C := C) z)
      (nonnegativeCochainEmbedding.extendFunctor (ModuleCat.{u} C)) ≫
    (nonnegativeSingleExtendNatIso (C := C)).hom

/-- The actual standard map from the parameter/colimit model to the original parameter Koszul. -/
def parameterKoszulColimitToKoszul {r : ℕ} (y : Fin r → C) :
    parameterKoszulColimitFunctor z y ⟶ koszulModuleFunctor y :=
  Functor.whiskerRight (algebraKoszulDualIntegerToSingle (C := C) z) (koszulFunctor y)

end SerrePositivity
