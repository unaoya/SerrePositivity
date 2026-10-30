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

end SerrePositivity
