module
public import SerrePositivity.HomologicalAlgebra.AlgebraKoszulBounds
public import SerrePositivity.HomologicalAlgebra.ConeLES

/-! # Explicit ideal powers annihilating iterated scalar-cone homology -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {R : Type u} [CommRing R]

/-- In an exact three-term sequence the product of endpoint annihilators kills the middle. -/
lemma ideal_mul_le_annihilator_of_exact (S : ShortComplex (ModuleCat.{u} R)) (hS : S.Exact)
    (I J : Ideal R) (hI : I ≤ Module.annihilator R S.X₁)
    (hJ : J ≤ Module.annihilator R S.X₃) : I * J ≤ Module.annihilator R S.X₂ := by
  apply Ideal.mul_le.mpr
  intro a ha b hb
  rw [Module.mem_annihilator]
  intro x
  have hx : S.g (b • x) = 0 := by
    rw [map_smul]
    exact (Module.mem_annihilator.mp (hJ hb)) _
  obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff S).mp hS (b • x) hx
  rw [mul_smul, ← hy, ← map_smul, Module.mem_annihilator.mp (hI ha) y, map_zero]

/-- Adjacent endpoint annihilators multiply along the actual mapping-cone long exact sequence. -/
lemma mappingCone_homology_annihilator_mul
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L) (q : ℤ)
    (I J : Ideal R) (hI : I ≤ Module.annihilator R (L.homology q))
    (hJ : J ≤ Module.annihilator R (K.homology (q + 1))) :
    I * J ≤ Module.annihilator R ((CochainComplex.mappingCone f).homology q) :=
  ideal_mul_le_annihilator_of_exact _ (Cone.exact₃ f q (q + 1) rfl) I J hI hJ

/-- Each parameter scalar cone doubles the sufficient ideal-power exponent on low homology. -/
lemma koszulComplexOn_homology_annihilator_pow
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (I : Ideal R) (b : ℤ)
    (hK : ∀ q, q < b → I ≤ Module.annihilator R (K.homology q)) :
    ∀ {r : ℕ} (y : Fin r → R) (q : ℤ), q < b - (r : ℤ) →
      I ^ (2 ^ r) ≤ Module.annihilator R ((koszulComplexOn y K).homology q)
  | 0, _, q, hq => by
    change I ^ (2 ^ 0) ≤ Module.annihilator R (K.homology q)
    simpa only [pow_zero, pow_one] using hK q (by simpa using hq)
  | r + 1, y, q, hq => by
    have h₀ := koszulComplexOn_homology_annihilator_pow K I b hK (Fin.init y) q
      (by omega)
    have h₁ := koszulComplexOn_homology_annihilator_pow K I b hK (Fin.init y) (q + 1)
      (by omega)
    have h := mappingCone_homology_annihilator_mul
      (smulId (y (Fin.last r)) (koszulComplexOn (Fin.init y) K)) q _ _ h₀ h₁
    have hpow : I ^ (2 ^ (r + 1)) = I ^ (2 ^ r) * I ^ (2 ^ r) := by
      rw [pow_succ (2 : ℕ) r, pow_mul, pow_two]
    rw [hpow]
    exact h

/-- Full higher-Tor annihilation gives an explicit power on the actual parameter/colimit model. -/
lemma parameterKoszulColimit_homology_annihilator_pow_of_tor_annihilated
    {C : Type u} [CommRing C] [Algebra R C] [IsNoetherian R R]
    {e : ℕ} (z : Fin e → R)
    (hres : ∀ n : ℕ, IsKoszulResolution (fun j => z j ^ n)) (I : Ideal C)
    (hTor : ∀ (N : ModuleCat.{u} R) (j : ℕ), 0 < j →
      ∀ c ∈ I, torCoefficientScalarEndomorphism C N j c = 0)
    {r : ℕ} (y : Fin r → C) (q : ℤ) (hq : q < (e : ℤ) - (r : ℤ)) :
    I ^ (2 ^ r) ≤ Module.annihilator C
      (((parameterKoszulColimitFunctor z y).obj (ModuleCat.of C C)).homology q) := by
  apply koszulComplexOn_homology_annihilator_pow _ I (e : ℤ) _ y q hq
  intro j hj
  by_cases hneg : j < 0
  · have hz := (((algebraKoszulDualIntegerColimitFunctor (C := C) z).obj
        (ModuleCat.of C C)).sc j).isZero_homology_of_isZero_X₂
      (algebraKoszulDualIntegerColimit_isZero_X_of_neg z (ModuleCat.of C C) j hneg)
    have : Subsingleton
        (((algebraKoszulDualIntegerColimitFunctor (C := C) z).obj
          (ModuleCat.of C C)).homology j) := ModuleCat.subsingleton_of_isZero hz
    intro c hc
    rw [Module.mem_annihilator]
    intro x
    exact Subsingleton.elim _ _
  · have heq : (j.toNat : ℤ) = j := Int.toNat_of_nonneg (by omega)
    rw [← heq]
    exact algebraKoszulDualIntegerColimitHomology_annihilator_of_tor_annihilated
      z hres I hTor j.toNat (by omega)

/-- For a length-e parameter sequence every negative homology of the total model is killed. -/
lemma parameterKoszulColimit_negative_homology_annihilator_pow
    {C : Type u} [CommRing C] [Algebra R C] [IsNoetherian R R]
    {e : ℕ} (z : Fin e → R)
    (hres : ∀ n : ℕ, IsKoszulResolution (fun j => z j ^ n)) (I : Ideal C)
    (hTor : ∀ (N : ModuleCat.{u} R) (j : ℕ), 0 < j →
      ∀ c ∈ I, torCoefficientScalarEndomorphism C N j c = 0)
    (y : Fin e → C) (q : ℤ) (hq : q < 0) :
    I ^ (2 ^ e) ≤ Module.annihilator C
      (((parameterKoszulColimitFunctor z y).obj (ModuleCat.of C C)).homology q) :=
  parameterKoszulColimit_homology_annihilator_pow_of_tor_annihilated
    z hres I hTor y q (by simpa using hq)

end SerrePositivity
