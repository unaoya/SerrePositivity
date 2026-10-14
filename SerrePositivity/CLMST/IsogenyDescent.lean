module
public import SerrePositivity.HomologicalAlgebra.CompleteFaithfullyFlatDescent
public import SerrePositivity.CLMST.FiniteFreeConeIsogeny

/-! # Conditional isogeny descent from a specified completely faithfully flat extension -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity.CLMST
open CategoryTheory CategoryTheory.Limits DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
variable {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- The actual cone of a module morphism as a bounded-above derived object. -/
def moduleMapConeBoundedAbove (f : M →ₗ[R] N) : DerivedCategory.Minus (ModuleCat.{u} R) :=
  ⟨moduleMapCone R f, ⟨0, by
    change (DerivedCategory.Q.obj (moduleMapConeComplex R f)).IsLE 0
    infer_instance⟩⟩

/-- Uniform annihilation in the three relevant degrees after extension gives a scalar zero cone. -/
theorem moduleMapConeScalar_descent (a : R)
    (hS : IsCompletelyFaithfullyFlat (Ideal.span {a}) (baseChangeScalarModule φ))
    (f : M →ₗ[R] N) (hC : IsComplete R a (moduleMapCone R f)) (g : R) (q : ℕ)
    (h : ∀ n : ℕ, ∀ i ∈ Set.Icc (-2 : ℤ) 0,
      ∀ x : (DerivedCategory.homologyFunctor (ModuleCat S) i).obj
        ((boundedAboveDerivedBaseChange φ).obj
          ((boundedAboveDerivedScalarCone R (a ^ n)).obj (moduleMapConeBoundedAbove f))).obj,
        (φ g) ^ q • x = 0) :
    moduleMapConeScalar R f (g ^ (4 * q)) = 0 := by
  let X := moduleMapConeBoundedAbove f
  have : X.obj.IsGE (-1) := by
    change (DerivedCategory.Q.obj (moduleMapConeComplex R f)).IsGE (-1)
    infer_instance
  have : X.obj.IsLE 0 := by
    change (DerivedCategory.Q.obj (moduleMapConeComplex R f)).IsLE 0
    infer_instance
  apply complete_two_cohomology_scalar_pow_eq_zero_of_completelyFaithfullyFlat
    φ a hS X hC (-1) 0 (by decide) g q
  intro n i hi
  apply h n i
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
  rcases hi with hi | hi | hi | hi <;> subst i <;> norm_num

/-- Isogeny descent with a specified extension and a uniform annihilator. -/
theorem moduleMapConeIsogeny_descent (a : R)
    (hS : IsCompletelyFaithfullyFlat (Ideal.span {a}) (baseChangeScalarModule φ))
    (f : M →ₗ[R] N) (hC : IsComplete R a (moduleMapCone R f)) (g : R)
    (h : ∃ q : ℕ, ∀ n : ℕ, ∀ i ∈ Set.Icc (-2 : ℤ) 0,
      ∀ x : (DerivedCategory.homologyFunctor (ModuleCat S) i).obj
        ((boundedAboveDerivedBaseChange φ).obj
          ((boundedAboveDerivedScalarCone R (a ^ n)).obj (moduleMapConeBoundedAbove f))).obj,
        (φ g) ^ q • x = 0) :
    ∃ q : ℕ, moduleMapConeScalar R f (g ^ q) = 0 ∧
      (∀ x : f.ker, g ^ q • x = 0) ∧ (∀ x : N ⧸ f.range, g ^ q • x = 0) := by
  obtain ⟨q, hq⟩ := h
  have hz := moduleMapConeScalar_descent φ a hS f hC g q hq
  exact ⟨4 * q, hz, moduleMapCone_pow_scalar_eq_zero_annihilates R f g (4 * q) hz⟩

/-- If g acts regularly on the source, the descended isogeny is injective. -/
theorem moduleMapConeIsogeny_descent_injective (a : R)
    (hS : IsCompletelyFaithfullyFlat (Ideal.span {a}) (baseChangeScalarModule φ))
    (f : M →ₗ[R] N) (hC : IsComplete R a (moduleMapCone R f)) (g : R)
    (hg : IsSMulRegular M g)
    (h : ∃ q : ℕ, ∀ n : ℕ, ∀ i ∈ Set.Icc (-2 : ℤ) 0,
      ∀ x : (DerivedCategory.homologyFunctor (ModuleCat S) i).obj
        ((boundedAboveDerivedBaseChange φ).obj
          ((boundedAboveDerivedScalarCone R (a ^ n)).obj (moduleMapConeBoundedAbove f))).obj,
        (φ g) ^ q • x = 0) :
    Function.Injective f ∧ ∃ q : ℕ, ∀ x : N ⧸ f.range, g ^ q • x = 0 := by
  obtain ⟨q, hq, _, _⟩ := moduleMapConeIsogeny_descent φ a hS f hC g h
  obtain ⟨hf, hc⟩ := moduleMapCone_pow_scalar_eq_zero_injective_of_regular R f g q hg hq
  exact ⟨hf, q, hc⟩

/-- E5 supplies the uniform exponent if the extended reductions compare to a finite-free cone. -/
theorem finiteFreeConeIsogeny_descent [IsReduced S]
    (a : R) (hS : IsCompletelyFaithfullyFlat (Ideal.span {a}) (baseChangeScalarModule φ))
    (f : M →ₗ[R] N) (hC : IsComplete R a (moduleMapCone R f)) (g : R)
    {L : Type u} [AddCommGroup L] [Module S L] [Module.Finite S L]
    (r : ℕ) (u : L →ₗ[S] (Fin r → S))
    (hu : Function.Bijective (awayModuleMap (φ g) u))
    (comparison : ∀ n : ℕ,
      ((boundedAboveDerivedBaseChange φ).obj
        ((boundedAboveDerivedScalarCone R (a ^ n)).obj (moduleMapConeBoundedAbove f))).obj ≅
      (derivedScalarConeFunctor S ((φ a) ^ n)).obj (moduleMapCone S u)) :
    ∃ q : ℕ, moduleMapConeScalar R f (g ^ q) = 0 ∧
      (∀ x : f.ker, g ^ q • x = 0) ∧ (∀ x : N ⧸ f.range, g ^ q • x = 0) := by
  obtain ⟨q, hq⟩ := finiteFreeConeIsogeny S (φ g) r u hu
  apply moduleMapConeIsogeny_descent φ a hS f hC g
  refine ⟨q, fun n i hi x => ?_⟩
  let e := (DerivedCategory.homologyFunctor (ModuleCat S) i).mapIso (comparison n)
  have hc := derivedScalarCone_homology_annihilated_of_scalar_eq_zero S
    ((φ a) ^ n) (moduleMapCone S u) ((φ g) ^ q) hq i
  apply e.toLinearEquiv.injective
  simp only [map_smul, map_zero]
  exact hc (e.hom x)

end SerrePositivity.CLMST
