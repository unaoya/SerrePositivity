module
public import SerrePositivity.HomologicalAlgebra.LocalCohomology.BaseChange
public import SerrePositivity.CLMST.FiniteStageKoszulAnnihilator

/-! # Conditional form of the two conclusions of CLMST Corollary 4.0.4

All higher Tor annihilation and quotient-image idempotence inputs remain explicit.
The theorem uses actual maximal-ideal local cohomology and all actual finite stages.
-/
@[expose] public noncomputable section
universe u
namespace SerrePositivity.CLMST
open CategoryTheory Section2

/-- The two conclusions of Corollary 4.0.4 follow from the explicit common inputs,
without using the literature statement or any perfectoid existence input in the proof. -/
lemma conditional_corollary_4_0_4
    {A D C S : Type u} [CommRing A] [IsNoetherianRing A]
    [CommRing D] [IsLocalRing D] [IsNoetherianRing D] [CommRing C] [CommRing S]
    [Algebra A D] [Module.Finite A D] [Algebra A C] [Algebra D C] [IsScalarTower A D C]
    {e : ℕ} (t : Fin e → A) (p : ℕ) [Fact p.Prime]
    (hsop : IsSystemOfParameters D (algebraMap A D ∘ t))
    (hres : ∀ k : ℕ, IsKoszulResolution (fun j => t j ^ k))
    (φ : ∀ n : ℕ, Section2.StageAlgebra A D t p n →+* C)
    (hφ : ∀ (n : ℕ) (x : A), φ n (algebraMap D (Section2.StageAlgebra A D t p n)
      (algebraMap A D x)) = algebraMap A C x)
    (ψ : S →+* C) (I : Ideal S) (a : S) (j₀ : Fin e)
    (ha : ψ a = algebraMap A C (t j₀))
    (hI : ∀ k : ℕ, 0 < k →
      IsIdempotentElem (I.map (Ideal.Quotient.mk (Ideal.span {a ^ k}))))
    (hTor : ∀ (N : ModuleCat.{u} A) (j : ℕ), 0 < j →
      ∀ s ∈ I, torCoefficientScalarEndomorphism C N j (ψ s) = 0) :
    (∀ i : ℕ, i < e → ∀ s ∈ I,
      HomologicalAlgebra.localCohomologyScalarEndomorphism
        (IsLocalRing.maximalIdeal D) i C (ψ s) = 0) ∧
    (∀ n : ℕ,
      let _ := Section2.stageAlgebra_isLocalRing_of_parameters A D t p hsop n
      ∀ (y : Fin e → Section2.StageAlgebra A D t p n),
        IsSystemOfParameters (Section2.StageAlgebra A D t p n) y → ∀ i : ℕ, 0 < i →
          let _ := Module.compHom (koszulHomologySelf (φ n ∘ y) i) ψ
          I ≤ Module.annihilator S (koszulHomologySelf (φ n ∘ y) i)) := by
  constructor
  · intro i hi s hs
    exact parameterLocalCohomologyScalarEndomorphism_eq_zero_of_baseIdeal_tor
      ψ I t hsop hres hTor i hi s hs
  · intro n
    exact finiteStageKoszul_positive_annihilator t p hsop hres n (φ n) (hφ n)
      ψ I a j₀ ha hI hTor

end SerrePositivity.CLMST
