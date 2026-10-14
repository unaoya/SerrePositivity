module

public import SerrePositivity.CommutativeAlgebra.CubicCyclotomicClosedFiber

/-! # The cubic cyclotomic local closed fiber is a field -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open Polynomial IsLocalRing
variable {R : Type u} [CommRing R] [IsLocalRing R]
    (g h : (ResidueField R)[X])
    (hf : cubicCyclotomicPolynomial (ResidueField R) = g * h)
    [Fact (Irreducible g)]

/-- The selected factor point, expressed as the pullback of its point on the closed fiber. -/
def cubicCyclotomicFactorPoint : Ideal (CubicCyclotomicAlgebra R) :=
  (adjoinRootFactorIdeal g h).comap (cubicCyclotomicFiberMap g h hf)

instance cubicCyclotomicFactorPoint_isMaximal : (cubicCyclotomicFactorPoint g h hf).IsMaximal :=
  Ideal.comap_isMaximal_of_surjective (cubicCyclotomicFiberMap g h hf)
    (cubicCyclotomicFiberMap_surjective g h hf)

lemma cubicCyclotomicFactorPoint_comap :
    (cubicCyclotomicFactorPoint g h hf).comap
      (algebraMap R (CubicCyclotomicAlgebra R)) = maximalIdeal R := by
  ext r
  change adjoinRootFactorMap g h (cubicCyclotomicFiberMap g h hf
    (AdjoinRoot.of (cubicCyclotomicPolynomial R) r)) = 0 ↔ r ∈ maximalIdeal R
  simp only [cubicCyclotomicFiberMap, AdjoinRoot.map_of,
    adjoinRootFactorMap, AdjoinRoot.map_of, RingHom.id_apply]
  rw [map_eq_zero_iff (AdjoinRoot.of g) (AdjoinRoot.of g).injective, residue_eq_zero_iff]

variable (B : Type u) [CommRing B] [Algebra (CubicCyclotomicAlgebra R) B]
    [Algebra R B] [IsScalarTower R (CubicCyclotomicAlgebra R) B]
    [hB : IsLocalization (cubicCyclotomicFactorPoint g h hf).primeCompl B]

include hB

/-- At the selected point the local closed fiber is the irreducible factor field. -/
lemma cubicCyclotomicLocalFiber_isField (hc : IsCoprime g h) :
    IsField (B ⧸ (maximalIdeal R).map (algebraMap R B)) := by
  let π := cubicCyclotomicFiberMap g h hf
  have hp : Function.Surjective π := cubicCyclotomicFiberMap_surjective g h hf
  let T := B ⧸ (RingHom.ker π).map (algebraMap (CubicCyclotomicAlgebra R) B)
  let : IsLocalization ((adjoinRootFactorIdeal g h).comap π).primeCompl B := hB
  let : Algebra (AdjoinRoot (g * h)) T := localizedSurjectiveQuotientAlgebra π hp B
  let : IsLocalization (adjoinRootFactorIdeal g h).primeCompl T :=
    isLocalization_localizedSurjectiveQuotient π hp B (adjoinRootFactorIdeal g h)
  have hfield : IsField T := isField_coprimeFactorLocalization g h T hc
  have hm : (RingHom.ker π).map (algebraMap (CubicCyclotomicAlgebra R) B) =
      (maximalIdeal R).map (algebraMap R B) := by
    rw [cubicCyclotomicFiberMap_ker, Ideal.map_map,
      ← IsScalarTower.algebraMap_eq R (CubicCyclotomicAlgebra R) B]
  change IsField (B ⧸ (RingHom.ker π).map (algebraMap (CubicCyclotomicAlgebra R) B)) at hfield
  rw [hm] at hfield
  exact hfield

/-- Fieldness of the closed fiber identifies the extended maximal ideal. -/
lemma cubicCyclotomicLocal_map_maximalIdeal [IsLocalRing B] (hc : IsCoprime g h) :
    (maximalIdeal R).map (algebraMap R B) = maximalIdeal B := by
  have hi := Ideal.Quotient.maximal_of_isField ((maximalIdeal R).map (algebraMap R B))
    (cubicCyclotomicLocalFiber_isField g h hf B hc)
  exact eq_maximalIdeal hi

end SerrePositivity
