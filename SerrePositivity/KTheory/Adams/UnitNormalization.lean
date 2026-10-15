module

public import SerrePositivity.KTheory.Adams.KoszulTensor
public import SerrePositivity.PerfectComplex.IdempotentImageTrivial

/-! # The cyclic square preserves the class of the degree-zero unit complex -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory Category Limits MonoidalCategory HomologicalComplex
open scoped TensorProduct
variable {R : Type u} [CommRing R]
namespace Adams

lemma scalarModule_braiding_id :
    (β_ (ModuleCat.of R R) (ModuleCat.of R R)).hom = 𝟙 _ := by
  apply (cancel_mono (λ_ (ModuleCat.of R R)).hom).mp
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  change y * x = x * y
  exact mul_comm y x

lemma oneKoszulUnitXZero_braiding_id :
    (β_ ((oneKoszulUnit (R := R)).X 0) ((oneKoszulUnit (R := R)).X 0)).hom = 𝟙 _ := by
  let e := oneKoszulUnitSelfIso (R := R)
  have : IsIso (e.hom ⊗ₘ e.hom) :=
    inferInstanceAs (IsIso (MonoidalCategory.tensorIso e e).hom)
  apply (cancel_mono (e.hom ⊗ₘ e.hom)).mp
  rw [← BraidedCategory.braiding_naturality, scalarModule_braiding_id,
    Category.comp_id, Category.id_comp]

lemma tensorSquareUnit_swap : tensorSquareSwap (oneKoszulUnit (R := R)) = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j h
  by_cases hi : i = 0
  · subst i
    by_cases hj : j = 0
    · subst j
      have hn : n = 0 := by dsimp at h; omega
      subst n
      rw [ιTensorObj_tensorSquareSwap]
      simp [oneKoszulUnitXZero_braiding_id]
    · have hz := isZero_single_obj_X (.up ℤ) 0 (ModuleCat.of R R) j hj
      exact ((tensorLeft ((oneKoszulUnit (R := R)).X 0)).map_isZero hz).eq_of_src _ _
  · have hz := isZero_single_obj_X (.up ℤ) 0 (ModuleCat.of R R) i hi
    exact ((tensorRight ((oneKoszulUnit (R := R)).X j)).map_isZero hz).eq_of_src _ _

lemma oneKoszulUnit_perfect : strictlyPerfectComplex R (oneKoszulUnit (R := R)) :=
  (isPerfectSupported_koszulComplex (fun i : Fin 0 => Fin.elim0 i)).strictlyPerfect

lemma oneKoszulUnit_support :
    HasHomologySupportOn (⊤ : TopologicalSpace.Closeds (PrimeSpectrum R))
      (oneKoszulUnit (R := R)) :=
  fun _ => Set.subset_univ _

def cyclicUnitClass : K0WithSupport (⊤ : TopologicalSpace.Closeds (PrimeSpectrum R)) :=
  K0WithSupport.mk ⊤ (supportedPerfectOnObj ⊤ (oneKoszulUnit (R := R))
    oneKoszulUnit_perfect oneKoszulUnit_support)

variable [Invertible (2 : R)]

lemma tensorSquareUnit_positive_map :
    (tensorSquarePositiveProjector (oneKoszulUnit (R := R))).map = 𝟙 _ := by
  rw [tensorSquarePositiveProjector_map, tensorSquareUnit_swap, ← two_smul R,
    smul_smul, invOf_mul_self, one_smul]

lemma tensorSquareUnit_negative_map :
    (tensorSquareNegativeProjector (oneKoszulUnit (R := R))).map = 0 := by
  change 𝟙 _ - (tensorSquarePositiveProjector (oneKoszulUnit (R := R))).map = 0
  rw [tensorSquareUnit_positive_map, sub_self]

def tensorSquareUnitPositiveIso :
    tensorSquarePositive (oneKoszulUnit (R := R)) ≅ oneKoszulUnit :=
  (tensorSquarePositiveProjector oneKoszulUnit).imageIsoOfMapEqId tensorSquareUnit_positive_map ≪≫
    cochainTensorLeftUnitor oneKoszulUnit

lemma tensorSquareUnitNegative_isZero :
    IsZero (tensorSquareNegative (oneKoszulUnit (R := R))) :=
  (tensorSquareNegativeProjector oneKoszulUnit).image_isZero_of_map_eq_zero
    tensorSquareUnit_negative_map

lemma tensorSquareClass_unit_on (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (hs : HasHomologySupportOn Z (oneKoszulUnit (R := R))) :
    tensorSquareClass (oneKoszulUnit (R := R)) Z oneKoszulUnit_perfect hs =
      K0WithSupport.mk Z (supportedPerfectOnObj Z oneKoszulUnit oneKoszulUnit_perfect hs) := by
  have hpos := K0WithSupport.mk_eq_of_quasiIso Z
    (tensorSquarePositive (oneKoszulUnit (R := R))) oneKoszulUnit
    (tensorSquarePositive_perfect _ oneKoszulUnit_perfect) oneKoszulUnit_perfect
    (tensorSquarePositive_support oneKoszulUnit_perfect hs) hs
    (tensorSquareUnitPositiveIso (R := R)).hom
  have hneg := K0WithSupport.mk_eq_zero_of_isZero Z
    (tensorSquareNegative_perfect _ oneKoszulUnit_perfect)
    (tensorSquareNegative_support oneKoszulUnit_perfect hs) tensorSquareUnitNegative_isZero
  have he := congrArg₂ (fun x y : K0WithSupport Z => x - y) hpos hneg
  exact he.trans (by simp)

lemma tensorSquareClass_unit :
    tensorSquareClass (oneKoszulUnit (R := R)) ⊤ oneKoszulUnit_perfect oneKoszulUnit_support =
      cyclicUnitClass :=
  tensorSquareClass_unit_on ⊤ oneKoszulUnit_support

lemma cyclicTwo_unit : cyclicTwo ⊤ (cyclicUnitClass (R := R)) = cyclicUnitClass :=
  (cyclicTwo_mk_concrete ⊤ (oneKoszulUnit (R := R)) oneKoszulUnit_perfect
    oneKoszulUnit_support).trans tensorSquareClass_unit

end Adams
end SerrePositivity
