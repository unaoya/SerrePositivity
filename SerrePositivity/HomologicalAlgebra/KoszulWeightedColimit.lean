module
public import SerrePositivity.HomologicalAlgebra.ScalarWeightedColimit
public import SerrePositivity.HomologicalAlgebra.KoszulRadicalSupport

/-! # Parameter Koszul acyclicity of actual scalar-weighted colimits -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {D C : Type u} [CommRing D] [CommRing C]

/-- Every power of an invertible module scalar remains invertible as an actual module map. -/
lemma moduleScalar_pow_isIso (M : ModuleCat.{u} C) (a : C)
    [IsIso (a • 𝟙 M)] (n : ℕ) : IsIso (a ^ n • 𝟙 M) := by
  induction n with
  | zero => simp only [pow_zero, one_smul]; infer_instance
  | succ n ih =>
    have h : a ^ (n + 1) • 𝟙 M = (a ^ n • 𝟙 M) ≫ (a • 𝟙 M) := by
      simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp, smul_smul,
        pow_succ, mul_comm]
    rw [h]
    infer_instance

/-- A parameter-radical element acting invertibly on coefficients forces all actual
Koszul homology to vanish. The element need not be a unit in the coefficient ring. -/
lemma koszulModuleHomology_isZero_of_scalar_isIso (φ : D →+* C)
    {r : ℕ} (y : Fin r → D) (a : D) (ha : a ∈ (Ideal.span (Set.range y)).radical)
    (M : ModuleCat.{u} C) [IsIso (φ a • 𝟙 M)] (q : ℤ) :
    IsZero (((koszulModuleFunctor (φ ∘ y)).obj M).homology q) := by
  obtain ⟨n, _, hn⟩ :=
    koszulModuleHomology_uniform_power_annihilator_of_mem_radical φ y a ha
  have := moduleScalar_pow_isIso M (φ a) n
  have hmap : homologyMap ((koszulModuleFunctor (φ ∘ y)).map (φ a ^ n • 𝟙 M)) q =
      φ a ^ n • 𝟙 (((koszulModuleFunctor (φ ∘ y)).obj M).homology q) := by
    rw [CategoryTheory.Functor.map_smul, CategoryTheory.Functor.map_id,
      homologyMap_smul, homologyMap_id]
  have : IsIso (φ a ^ n • 𝟙 (((koszulModuleFunctor (φ ∘ y)).obj M).homology q)) :=
    hmap ▸ (inferInstance : IsIso
      (homologyMap ((koszulModuleFunctor (φ ∘ y)).map (φ a ^ n • 𝟙 M)) q))
  apply IsZero.of_epi_eq_zero (φ a ^ n • 𝟙 _)
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact Module.mem_annihilator.mp (hn M q) x

/-- The actual weighted colimit is Koszul-acyclic when its weight lies in the
parameter radical, uniformly for every degree and every sequence of coefficients. -/
lemma koszulWeightedColimit_homology_isZero (φ : D →+* C)
    {r : ℕ} (y : Fin r → D) (a : D) (ha : a ∈ (Ideal.span (Set.range y)).radical)
    (X : ℕ → ModuleCat.{u} C) (t : ∀ n, X n ⟶ X (n + 1)) (q : ℤ) :
    IsZero (((koszulModuleFunctor (φ ∘ y)).obj
      (colimit (scalarWeightedSequence (φ a) X t))).homology q) :=
  koszulModuleHomology_isZero_of_scalar_isIso φ y a ha _ q

end SerrePositivity
