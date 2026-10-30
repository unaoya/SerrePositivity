module
public import SerrePositivity.HomologicalAlgebra.ParameterKoszulComparison
public import SerrePositivity.HomologicalAlgebra.KoszulRadicalSupport
public import SerrePositivity.CommutativeAlgebra.Idempotent
public import SerrePositivity.HomologicalAlgebra.TorCoefficientIdeal

/-! # Removing annihilator powers in actual parameter Koszul homology -/
@[expose] public section
noncomputable section
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R C : Type u} [CommRing R] [CommRing C] [Algebra R C] [IsNoetherian R R]
/-- Quotient-image idempotence removes the finite-cone annihilator exponent. -/
lemma parameterKoszulHomology_annihilator_of_tor_and_idempotent
    {e r : ℕ} (z : Fin e → R) (y : Fin r → C)
    (hz : ∀ j, algebraMap R C (z j) ∈ (Ideal.span (Set.range y)).radical)
    (hres : ∀ n : ℕ, IsKoszulResolution (fun j => z j ^ n)) (I : Ideal C)
    (hTor : ∀ (N : ModuleCat.{u} R) (j : ℕ), 0 < j →
      ∀ c ∈ I, torCoefficientScalarEndomorphism C N j c = 0)
    (a : C) (ha : a ∈ (Ideal.span (Set.range y)).radical)
    (hI : ∀ n : ℕ, 0 < n →
      IsIdempotentElem (I.map (Ideal.Quotient.mk (Ideal.span {a ^ n}))))
    (q : ℤ) (hq : q < (e : ℤ) - (r : ℤ)) :
    I ≤ Module.annihilator C (((koszulModuleFunctor y).obj (ModuleCat.of C C)).homology q) := by
  have hpow := parameterKoszulHomology_annihilator_pow_of_tor_annihilated
    z y hz hres I hTor q hq
  obtain ⟨n, _, hn⟩ := koszulModuleHomology_uniform_power_annihilator_of_mem_radical
    (RingHom.id C) y a ha
  intro c hc
  rw [Module.mem_annihilator]
  apply ideal_annihilates_of_pow_annihilates_and_powerTorsion I a hI (2 ^ r)
    (pow_pos (by decide) r)
    (fun b hb x => Module.mem_annihilator.mp (hpow hb) x)
    (fun x => ⟨n, Module.mem_annihilator.mp (hn (ModuleCat.of C C) q) x⟩) c hc

/-- Every positive Koszul homology of a length-e sequence is killed by the ideal itself. -/
lemma parameterKoszulPositiveHomology_annihilator_of_tor_and_idempotent
    {e : ℕ} (z : Fin e → R) (y : Fin e → C)
    (hz : ∀ j, algebraMap R C (z j) ∈ (Ideal.span (Set.range y)).radical)
    (hres : ∀ n : ℕ, IsKoszulResolution (fun j => z j ^ n)) (I : Ideal C)
    (hTor : ∀ (N : ModuleCat.{u} R) (j : ℕ), 0 < j →
      ∀ c ∈ I, torCoefficientScalarEndomorphism C N j c = 0)
    (a : C) (ha : a ∈ (Ideal.span (Set.range y)).radical)
    (hI : ∀ n : ℕ, 0 < n →
      IsIdempotentElem (I.map (Ideal.Quotient.mk (Ideal.span {a ^ n}))))
    (i : ℕ) (hi : 0 < i) :
    I ≤ Module.annihilator C (koszulHomologySelf y i) := by
  have h := parameterKoszulHomology_annihilator_of_tor_and_idempotent
    z y hz hres I hTor a ha hI (-(i : ℤ)) (by omega)
  change I ≤ Module.annihilator C
    ((koszulComplexOn y ((HomologicalComplex.single (ModuleCat.{u} C) (.up ℤ) 0).obj
      (ModuleCat.of C C))).homology (-(i : ℤ))) at h
  rw [koszulComplexOn_single] at h
  exact h

/-- Original base-ideal hypotheses suffice after mapping the ideal to the coefficient ring. -/
lemma parameterKoszulHomology_imageIdeal_annihilator_of_tor_and_idempotent
    {S : Type u} [CommRing S] (φ : S →+* C) (I : Ideal S) (a : S)
    {e r : ℕ} (z : Fin e → R) (y : Fin r → C)
    (hz : ∀ j, algebraMap R C (z j) ∈ (Ideal.span (Set.range y)).radical)
    (hres : ∀ n : ℕ, IsKoszulResolution (fun j => z j ^ n))
    (hTor : ∀ (N : ModuleCat.{u} R) (j : ℕ), 0 < j →
      ∀ s ∈ I, torCoefficientScalarEndomorphism C N j (φ s) = 0)
    (ha : φ a ∈ (Ideal.span (Set.range y)).radical)
    (hI : ∀ n : ℕ, 0 < n →
      IsIdempotentElem (I.map (Ideal.Quotient.mk (Ideal.span {a ^ n}))))
    (q : ℤ) (hq : q < (e : ℤ) - (r : ℤ)) :
    I.map φ ≤ Module.annihilator C
      (((koszulModuleFunctor y).obj (ModuleCat.of C C)).homology q) := by
  apply parameterKoszulHomology_annihilator_of_tor_and_idempotent z y hz hres
    (I.map φ) _ (φ a) ha (quotient_power_images_idempotent_baseChange φ I a hI) q hq
  intro N j hj
  exact torCoefficientScalarEndomorphism_mapIdeal_eq_zero φ I N j (hTor N j hj)

/-- The image ideal kills every positive actual Koszul homology for equal-length sequences. -/
lemma parameterKoszulPositiveHomology_imageIdeal_annihilator_of_tor_and_idempotent
    {S : Type u} [CommRing S] (φ : S →+* C) (I : Ideal S) (a : S)
    {e : ℕ} (z : Fin e → R) (y : Fin e → C)
    (hz : ∀ j, algebraMap R C (z j) ∈ (Ideal.span (Set.range y)).radical)
    (hres : ∀ n : ℕ, IsKoszulResolution (fun j => z j ^ n))
    (hTor : ∀ (N : ModuleCat.{u} R) (j : ℕ), 0 < j →
      ∀ s ∈ I, torCoefficientScalarEndomorphism C N j (φ s) = 0)
    (ha : φ a ∈ (Ideal.span (Set.range y)).radical)
    (hI : ∀ n : ℕ, 0 < n →
      IsIdempotentElem (I.map (Ideal.Quotient.mk (Ideal.span {a ^ n}))))
    (i : ℕ) (hi : 0 < i) :
    I.map φ ≤ Module.annihilator C (koszulHomologySelf y i) := by
  apply parameterKoszulPositiveHomology_annihilator_of_tor_and_idempotent z y hz hres
    (I.map φ) _ (φ a) ha (quotient_power_images_idempotent_baseChange φ I a hI) i hi
  intro N j hj
  exact torCoefficientScalarEndomorphism_mapIdeal_eq_zero φ I N j (hTor N j hj)

/-- Restriction along the original map gives the base-ideal annihilator used in applications. -/
lemma parameterKoszulPositiveHomology_restricted_annihilator_of_tor_and_idempotent
    {S : Type u} [CommRing S] (φ : S →+* C) (I : Ideal S) (a : S)
    {e : ℕ} (z : Fin e → R) (y : Fin e → C)
    (hz : ∀ j, algebraMap R C (z j) ∈ (Ideal.span (Set.range y)).radical)
    (hres : ∀ n : ℕ, IsKoszulResolution (fun j => z j ^ n))
    (hTor : ∀ (N : ModuleCat.{u} R) (j : ℕ), 0 < j →
      ∀ s ∈ I, torCoefficientScalarEndomorphism C N j (φ s) = 0)
    (ha : φ a ∈ (Ideal.span (Set.range y)).radical)
    (hI : ∀ n : ℕ, 0 < n →
      IsIdempotentElem (I.map (Ideal.Quotient.mk (Ideal.span {a ^ n}))))
    (i : ℕ) (hi : 0 < i) :
    let _ := Module.compHom (koszulHomologySelf y i) φ
    I ≤ Module.annihilator S (koszulHomologySelf y i) := by
  let _ := Module.compHom (koszulHomologySelf y i) φ
  change I ≤ Module.annihilator S (koszulHomologySelf y i)
  have h := parameterKoszulPositiveHomology_imageIdeal_annihilator_of_tor_and_idempotent
    φ I a z y hz hres hTor ha hI i hi
  intro s hs
  rw [Module.mem_annihilator]
  intro x
  exact Module.mem_annihilator.mp (h (Ideal.mem_map_of_mem φ hs)) x

end SerrePositivity
