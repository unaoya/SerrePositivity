module
public import SerrePositivity.CommutativeAlgebra.FiniteParameters

/-! # Parameter support after an arbitrary coefficient ring map -/
@[expose] public section
universe u v
namespace SerrePositivity
variable {D : Type u} {C : Type v} [CommRing D] [CommRing C] [IsLocalRing D]

/-- A maximal-ideal element maps into the radical of every mapped parameter ideal. -/
lemma IsSystemOfParameters.map_mem_radical {r : ℕ} {y : Fin r → D}
    (hy : IsSystemOfParameters D y) (φ : D →+* C) {a : D}
    (ha : a ∈ IsLocalRing.maximalIdeal D) :
    φ a ∈ (Ideal.span (Set.range (φ ∘ y))).radical := by
  rw [← hy.2] at ha
  have h := Ideal.map_radical_le φ
    (Ideal.mem_map_of_mem φ ha)
  rw [Ideal.map_span, ← Set.range_comp] at h
  exact h

/-- The mapped coordinates of another parameter system have the required support. -/
lemma IsSystemOfParameters.map_coordinates_mem_radical {e r : ℕ} {z : Fin e → D}
    {y : Fin r → D} (hz : IsSystemOfParameters D z) (hy : IsSystemOfParameters D y)
    (φ : D →+* C) (j : Fin e) :
    φ (z j) ∈ (Ideal.span (Set.range (φ ∘ y))).radical := by
  apply hy.map_mem_radical φ
  rw [← hz.2]
  exact Ideal.le_radical (Ideal.subset_span (Set.mem_range_self j))

/-- Finite injective local extensions supply the support condition for any parameter system. -/
lemma IsSystemOfParameters.finite_map_coordinates_mem_radical
    {D E C : Type u} [CommRing D] [CommRing E] [CommRing C]
    [IsLocalRing D] [IsLocalRing E] [Algebra D E] [Module.Finite D E]
    (hinj : Function.Injective (algebraMap D E))
    {e r : ℕ} {z : Fin e → D} {y : Fin r → E}
    (hz : IsSystemOfParameters D z) (hy : IsSystemOfParameters E y)
    (φ : E →+* C) (j : Fin e) :
    φ (algebraMap D E (z j)) ∈ (Ideal.span (Set.range (φ ∘ y))).radical :=
  (hz.map_finite E hinj).map_coordinates_mem_radical hy φ j

end SerrePositivity
