module

public import SerrePositivity.CommutativeAlgebra.CubicCyclotomicFiber

/-! # A closed point of the cubic cyclotomic algebra above the local closed point -/

@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity
open Polynomial IsLocalRing

lemma adjoinRoot_map_mk {A : Type u} {K : Type v} [CommRing A] [CommRing K]
    (φ : A →+* K) (f : A[X]) (g : K[X]) (hdvd : g ∣ f.map φ) (q : A[X]) :
    AdjoinRoot.map φ f g hdvd (AdjoinRoot.mk f q) = AdjoinRoot.mk g (q.map φ) := by
  rw [AdjoinRoot.map, AdjoinRoot.lift_mk, ← Polynomial.eval₂_map]
  exact AdjoinRoot.aeval_eq (q.map φ)

lemma adjoinRoot_map_surjective {A : Type u} {K : Type v} [CommRing A] [CommRing K]
    (φ : A →+* K) (hφ : Function.Surjective φ) (f : A[X]) (g : K[X])
    (hdvd : g ∣ f.map φ) : Function.Surjective (AdjoinRoot.map φ f g hdvd) := by
  intro x
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective x
  obtain ⟨p, rfl⟩ := Polynomial.map_surjective φ hφ q
  exact ⟨AdjoinRoot.mk f p, adjoinRoot_map_mk φ f g hdvd p⟩

variable {R : Type u} [CommRing R] [IsLocalRing R]

lemma cubicCyclotomicPolynomial_map_residue :
    (cubicCyclotomicPolynomial R).map (residue R) = cubicCyclotomicPolynomial (ResidueField R) := by
  simp [cubicCyclotomicPolynomial]

/-- A residue factor gives the canonical surjective homomorphism to its field quotient. -/
def cubicCyclotomicResidueMap (g : (ResidueField R)[X])
    (hg : g ∣ cubicCyclotomicPolynomial (ResidueField R)) :
    CubicCyclotomicAlgebra R →+* AdjoinRoot g :=
  AdjoinRoot.map (residue R) (cubicCyclotomicPolynomial R) g
    (cubicCyclotomicPolynomial_map_residue (R := R) ▸ hg)

lemma cubicCyclotomicResidueMap_surjective (g : (ResidueField R)[X])
    (hg : g ∣ cubicCyclotomicPolynomial (ResidueField R)) :
    Function.Surjective (cubicCyclotomicResidueMap g hg) :=
  adjoinRoot_map_surjective _ (residue_surjective) _ _ _

lemma cubicCyclotomicResidueMap_algebraMap (g : (ResidueField R)[X])
    (hg : g ∣ cubicCyclotomicPolynomial (ResidueField R)) (r : R) :
    cubicCyclotomicResidueMap g hg (algebraMap R (CubicCyclotomicAlgebra R) r) =
      AdjoinRoot.of g (residue R r) := by
  exact AdjoinRoot.map_of _ _ _ _ r

/-- The field quotient makes the kernel a maximal ideal. -/
lemma cubicCyclotomicResidueMap_ker_isMaximal (g : (ResidueField R)[X])
    (hg : g ∣ cubicCyclotomicPolynomial (ResidueField R)) (hi : Irreducible g) :
    (RingHom.ker (cubicCyclotomicResidueMap g hg)).IsMaximal := by
  let : Fact (Irreducible g) := ⟨hi⟩
  exact RingHom.ker_isMaximal_of_surjective _ (cubicCyclotomicResidueMap_surjective g hg)

/-- The point lies over the original maximal ideal, with the structural map explicit. -/
lemma cubicCyclotomicResidueMap_ker_comap (g : (ResidueField R)[X])
    (hg : g ∣ cubicCyclotomicPolynomial (ResidueField R)) (hi : Irreducible g) :
    (RingHom.ker (cubicCyclotomicResidueMap g hg)).comap
      (algebraMap R (CubicCyclotomicAlgebra R)) = maximalIdeal R := by
  let : Fact (Irreducible g) := ⟨hi⟩
  ext r
  rw [Ideal.mem_comap, RingHom.mem_ker, cubicCyclotomicResidueMap_algebraMap]
  rw [map_eq_zero_iff (AdjoinRoot.of g) (AdjoinRoot.of g).injective, residue_eq_zero_iff]

/-- A maximal point above the closed point exists in residue characteristic two. -/
lemma exists_cubicCyclotomicClosedPoint (htwo : (2 : ResidueField R) = 0) :
    ∃ n : Ideal (CubicCyclotomicAlgebra R), n.IsMaximal ∧
      n.comap (algebraMap R (CubicCyclotomicAlgebra R)) = maximalIdeal R := by
  obtain ⟨g, h, _, hi, hf, _, _⟩ := exists_cubicCyclotomic_coprime_factor htwo
  have hg : g ∣ cubicCyclotomicPolynomial (ResidueField R) := ⟨h, hf⟩
  exact ⟨RingHom.ker (cubicCyclotomicResidueMap g hg),
    cubicCyclotomicResidueMap_ker_isMaximal g hg hi, cubicCyclotomicResidueMap_ker_comap g hg hi⟩

end SerrePositivity
