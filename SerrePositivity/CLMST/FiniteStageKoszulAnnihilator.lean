module
public import SerrePositivity.CommutativeAlgebra.RootTower.BaseChange
public import SerrePositivity.HomologicalAlgebra.Koszul.ParameterAnnihilators

/-! # Conditional positive Koszul annihilation on the actual CLMST finite stages

The target coefficient ring is explicit. No perfectoidization existence, almost flatness,
or quotient-image idempotence is silently supplied by a literature input.
-/
@[expose] public noncomputable section
universe u
namespace SerrePositivity.CLMST
open CategoryTheory Section2

/-- The actual finite stages provide all the parameter support hypotheses for KL4/KL5. -/
lemma finiteStageKoszul_positive_annihilator
    {A D C S : Type u} [CommRing A] [IsNoetherianRing A] [CommRing D] [IsLocalRing D]
    [CommRing C] [CommRing S] [Algebra A D] [Module.Finite A D] [Algebra A C]
    {e : ℕ} (t : Fin e → A) (p : ℕ) [Fact p.Prime]
    (hsop : IsSystemOfParameters D (algebraMap A D ∘ t))
    (hres : ∀ k : ℕ, IsKoszulResolution (fun j => t j ^ k))
    (n : ℕ) (φ : Section2.StageAlgebra A D t p n →+* C)
    (hφ : ∀ x : A, φ (algebraMap D (Section2.StageAlgebra A D t p n)
      (algebraMap A D x)) = algebraMap A C x)
    (ψ : S →+* C) (I : Ideal S) (a : S) (j₀ : Fin e)
    (ha : ψ a = algebraMap A C (t j₀))
    (hI : ∀ k : ℕ, 0 < k →
      IsIdempotentElem (I.map (Ideal.Quotient.mk (Ideal.span {a ^ k}))))
    (hTor : ∀ (N : ModuleCat.{u} A) (j : ℕ), 0 < j →
      ∀ s ∈ I, torCoefficientScalarEndomorphism C N j (ψ s) = 0) :
    let _ := Section2.stageAlgebra_isLocalRing_of_parameters A D t p hsop n
    ∀ (y : Fin e → Section2.StageAlgebra A D t p n),
      IsSystemOfParameters (Section2.StageAlgebra A D t p n) y → ∀ i : ℕ, 0 < i →
        let _ := Module.compHom (koszulHomologySelf (φ ∘ y) i) ψ
        I ≤ Module.annihilator S (koszulHomologySelf (φ ∘ y) i) := by
  let _ := Section2.stageAlgebra_isLocalRing_of_parameters A D t p hsop n
  dsimp only
  intro y hy i hi
  exact finiteParameterKoszul_positive_annihilator
    (Section2.stageAlgebra_algebraMap_injective A D t p n) φ hφ t hsop hres
    ψ I a j₀ ha hI hTor y hy i hi

end SerrePositivity.CLMST
