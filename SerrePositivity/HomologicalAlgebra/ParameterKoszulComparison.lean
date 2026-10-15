module
public import SerrePositivity.HomologicalAlgebra.BoundedKoszulAugmentation
public import SerrePositivity.HomologicalAlgebra.AlgebraKoszulAugmentationZero
public import SerrePositivity.HomologicalAlgebra.AlgebraKoszulTermColimit
public import SerrePositivity.HomologicalAlgebra.KoszulHomologyAnnihilator

/-! # Actual parameter Koszul comparison and higher-Tor annihilator powers -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {R C : Type u} [CommRing R] [CommRing C] [Algebra R C]
variable {e r : ℕ} (z : Fin e → R) (y : Fin r → C)

/-- The actual canonical augmentation becomes a quasi-isomorphism after arbitrary parameter
Koszul operators when the standard coordinate images lie in the parameter radical. -/
lemma parameterKoszulColimitToKoszul_quasiIso
    (hz : ∀ j, algebraMap R C (z j) ∈ (Ideal.span (Set.range y)).radical)
    (M : ModuleCat.{u} C) : QuasiIso ((parameterKoszulColimitToKoszul z y).app M) := by
  change QuasiIso ((koszulFunctor y).map
    ((algebraKoszulDualIntegerToSingle (C := C) z).app M))
  apply boundedKoszulAugmentation_quasiIso y _ M _ e
  · exact algebraKoszulDualIntegerColimit_isZero_X_of_neg z M
  · exact algebraKoszulDualIntegerColimit_isZero_X_of_gt z M
  · intro q hq p
    have hNat : 0 < q.toNat := by omega
    have h := algebraKoszulDualColimit_positive_term_koszulHomology_isZero
      z y hz M (q.toNat - 1) p
    rw [Nat.sub_add_cancel (by omega : 1 ≤ q.toNat)] at h
    exact h.of_iso
      (((koszulModuleFunctor y) ⋙ homologyFunctor (ModuleCat.{u} C) (.up ℤ) p).mapIso
        (((algebraKoszulDualColimitFunctor (C := C) z).obj M).extendXIso
          nonnegativeCochainEmbedding (i := q.toNat) (by
            change (q.toNat : ℤ) = q
            exact Int.toNat_of_nonneg (by omega))))

/-- The comparison is natural in actual C-module coefficients and uses the actual standard map. -/
def parameterKoszulColimitHomologyNatIso
    (hz : ∀ j, algebraMap R C (z j) ∈ (Ideal.span (Set.range y)).radical) (q : ℤ) :
    parameterKoszulColimitFunctor z y ⋙ homologyFunctor (ModuleCat.{u} C) (.up ℤ) q ≅
      koszulModuleFunctor y ⋙ homologyFunctor (ModuleCat.{u} C) (.up ℤ) q := by
  have : ∀ M : ModuleCat.{u} C,
      IsIso ((Functor.whiskerRight (parameterKoszulColimitToKoszul z y)
        (homologyFunctor (ModuleCat.{u} C) (.up ℤ) q)).app M) := fun M => by
    have := parameterKoszulColimitToKoszul_quasiIso z y hz M
    change IsIso (homologyMap ((parameterKoszulColimitToKoszul z y).app M) q)
    infer_instance
  have := NatIso.isIso_of_isIso_app
    (Functor.whiskerRight (parameterKoszulColimitToKoszul z y)
      (homologyFunctor (ModuleCat.{u} C) (.up ℤ) q))
  exact asIso (Functor.whiskerRight (parameterKoszulColimitToKoszul z y)
    (homologyFunctor (ModuleCat.{u} C) (.up ℤ) q))

/-- Full higher-Tor annihilation transfers to the actual arbitrary-parameter Koszul homology,
with the explicit positive exponent supplied by the scalar-cone induction. -/
lemma parameterKoszulHomology_annihilator_pow_of_tor_annihilated [IsNoetherian R R]
    (hz : ∀ j, algebraMap R C (z j) ∈ (Ideal.span (Set.range y)).radical)
    (hres : ∀ n : ℕ, IsKoszulResolution (fun j => z j ^ n)) (I : Ideal C)
    (hTor : ∀ (N : ModuleCat.{u} R) (j : ℕ), 0 < j →
      ∀ c ∈ I, torCoefficientScalarEndomorphism C N j c = 0)
    (q : ℤ) (hq : q < (e : ℤ) - (r : ℤ)) :
    I ^ (2 ^ r) ≤ Module.annihilator C (((koszulModuleFunctor y).obj
      (ModuleCat.of C C)).homology q) := by
  have hpow := parameterKoszulColimit_homology_annihilator_pow_of_tor_annihilated
    z hres I hTor y q hq
  let E := ((parameterKoszulColimitHomologyNatIso z y hz q).app
    (ModuleCat.of C C)).toLinearEquiv
  intro c hc
  rw [Module.mem_annihilator]
  intro x
  obtain ⟨v, rfl⟩ := E.surjective x
  rw [← E.map_smul, Module.mem_annihilator.mp (hpow hc), E.map_zero]

/-- For a length-e parameter sequence, every positive Koszul homology has this ideal-power
annihilator. No regularity on the coefficient algebra or on its parameter sequence is used. -/
lemma parameterKoszulPositiveHomology_annihilator_pow_of_tor_annihilated
    [IsNoetherian R R] (y : Fin e → C)
    (hz : ∀ j, algebraMap R C (z j) ∈ (Ideal.span (Set.range y)).radical)
    (hres : ∀ n : ℕ, IsKoszulResolution (fun j => z j ^ n)) (I : Ideal C)
    (hTor : ∀ (N : ModuleCat.{u} R) (j : ℕ), 0 < j →
      ∀ c ∈ I, torCoefficientScalarEndomorphism C N j c = 0)
    (i : ℕ) (hi : 0 < i) :
    I ^ (2 ^ e) ≤ Module.annihilator C (koszulHomologySelf y i) := by
  have h := parameterKoszulHomology_annihilator_pow_of_tor_annihilated z y hz hres I hTor
    (-(i : ℤ)) (by omega)
  change I ^ (2 ^ e) ≤ Module.annihilator C
    ((koszulComplexOn y ((HomologicalComplex.single (ModuleCat.{u} C) (.up ℤ) 0).obj
      (ModuleCat.of C C))).homology (-(i : ℤ))) at h
  rw [koszulComplexOn_single] at h
  exact h

end SerrePositivity
