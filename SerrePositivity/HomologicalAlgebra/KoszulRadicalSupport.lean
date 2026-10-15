module
public import SerrePositivity.HomologicalAlgebra.KoszulCoordinateControl
public import Mathlib.RingTheory.Ideal.Maps

/-! # Uniform power annihilation from the radical of a parameter ideal -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits
variable {D C : Type u} [CommRing D] [CommRing C]

/-- Radical membership before coefficient extension supplies a single power killing
all coefficient Koszul homology, uniformly in the module and the degree. -/
lemma koszulModuleHomology_uniform_power_annihilator_of_mem_radical
    (φ : D →+* C) {r : ℕ} (y : Fin r → D) (a : D)
    (ha : a ∈ (Ideal.span (Set.range y)).radical) :
    ∃ n : ℕ, 0 < n ∧ ∀ (M : ModuleCat.{u} C) (q : ℤ),
      φ a ^ n ∈ Module.annihilator C
        (((koszulModuleFunctor (φ ∘ y)).obj M).homology q) := by
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp ha
  refine ⟨n + 1, by omega, ?_⟩
  intro M q
  apply span_le_annihilator_koszulModuleHomology (φ ∘ y) M q
  have hmap : φ (a ^ (n + 1)) ∈ (Ideal.span (Set.range y)).map φ :=
    Ideal.mem_map_of_mem φ (by
      rw [pow_succ]
      exact Ideal.mul_mem_right a _ hn)
  simpa only [map_pow, Ideal.map_span, ← Set.range_comp] using hmap

/-- A finite list in the radical admits one positive exponent for all its coordinates,
all coefficient modules, and all homology degrees. -/
lemma koszulModuleHomology_uniform_coordinate_powers_of_radical
    (φ : D →+* C) {r s : ℕ} (y : Fin r → D) (z : Fin s → D)
    (hz : ∀ j, z j ∈ (Ideal.span (Set.range y)).radical) :
    ∃ n : ℕ, 0 < n ∧ ∀ (j : Fin s) (M : ModuleCat.{u} C) (q : ℤ),
      φ (z j) ^ n ∈ Module.annihilator C
        (((koszulModuleFunctor (φ ∘ y)).obj M).homology q) := by
  choose n hn hkill using fun j =>
    koszulModuleHomology_uniform_power_annihilator_of_mem_radical φ y (z j) (hz j)
  let N := 1 + ∑ j : Fin s, n j
  refine ⟨N, by dsimp [N]; omega, ?_⟩
  intro j M q
  have hle : n j ≤ N := by
    have h := Finset.single_le_sum (fun k _ => Nat.zero_le (n k)) (Finset.mem_univ j)
    dsimp [N]
    omega
  rw [show N = n j + (N - n j) by omega, pow_add]
  exact Ideal.mul_mem_right _ _ (hkill j M q)

/-- Once an element of the parameter radical becomes a unit, the actual coefficient
Koszul complex has zero homology in every degree, for arbitrary coefficient modules. -/
lemma koszulModuleHomology_isZero_of_unit_in_parameter_radical
    (φ : D →+* C) {r : ℕ} (y : Fin r → D) (a : D)
    (ha : a ∈ (Ideal.span (Set.range y)).radical) (hu : IsUnit (φ a))
    (M : ModuleCat.{u} C) (q : ℤ) :
    IsZero (((koszulModuleFunctor (φ ∘ y)).obj M).homology q) := by
  obtain ⟨n, _, hn⟩ :=
    koszulModuleHomology_uniform_power_annihilator_of_mem_radical φ y a ha
  have : Subsingleton (((koszulModuleFunctor (φ ∘ y)).obj M).homology q) :=
    subsingleton_of_forall_eq 0 (fun x => (hu.pow n).smul_eq_zero.mp
      (Module.mem_annihilator.mp (hn M q) x))
  exact ModuleCat.isZero_of_subsingleton _

end SerrePositivity
