module

public import SerrePositivity.CommutativeAlgebra.PullbackAnnihilator
public import SerrePositivity.CommutativeAlgebra.PerfectoidIdealCover

/-! # Original perfectoid-ideal annihilators from a ring pullback square

Only the bottom-left algebra needs to be perfectoid. Its map from the original
base kills the generator, so the universal perfectoid ideal kills it as well.
No excision square for a particular modification is asserted by this file.
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits

/-- An actual ring pullback with a perfectoid closed-side algebra gives almost
annihilation of the top map over the original perfectoid base. -/
theorem perfectoidIdeal_ker_coker_annihilated_of_isPullback
    {R A B C D : Type u} [CommRing R] [CommRing A] [CommRing B]
    [CommRing C] [CommRing D] [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]
    {p : ℕ} [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (f : A →ₐ[R] B) (l : A →ₐ[R] C) (r : B →ₐ[R] D) (b : C →ₐ[R] D)
    (hPB : IsPullback (CommRingCat.ofHom f.toRingHom) (CommRingCat.ofHom l.toRingHom)
      (CommRingCat.ofHom r.toRingHom) (CommRingCat.ofHom b.toRingHom))
    (hC : IsIntegralPerfectoid C p) (g : R) (hg : algebraMap R C g = 0) :
    (∀ s ∈ perfectoidIdeal R p hR g, ∀ x : f.toLinearMap.ker, s • x = 0) ∧
    (∀ s ∈ perfectoidIdeal R p hR g, ∀ y : B ⧸ f.toLinearMap.range, s • y = 0) := by
  have hI := perfectoidIdeal_le_ker_of_eq_zero R p hR hC (algebraMap R C) g hg
  exact ⟨fun s hs => (algHom_ker_coker_annihilated_of_isPullback f l r b hPB s (hI hs)).1,
    fun s hs => (algHom_ker_coker_annihilated_of_isPullback f l r b hPB s (hI hs)).2⟩

/-- The actual projection from the concrete fiber product is an almost
comparison when its closed-side factor is perfectoid and kills the generator. -/
theorem perfectoidIdeal_ker_coker_annihilated_pullbackFst
    {R B C D : Type u} [CommRing R] [CommRing B] [CommRing C] [CommRing D]
    [Algebra R B] [Algebra R C] [Algebra R D]
    {p : ℕ} [Fact p.Prime] (hR : IsIntegralPerfectoid R p)
    (r : B →ₐ[R] D) (b : C →ₐ[R] D)
    (hC : IsIntegralPerfectoid C p) (g : R) (hg : algebraMap R C g = 0) :
    (∀ s ∈ perfectoidIdeal R p hR g,
      ∀ x : (AlgHom.pullbackFst r b).toLinearMap.ker, s • x = 0) ∧
    (∀ s ∈ perfectoidIdeal R p hR g,
      ∀ y : B ⧸ (AlgHom.pullbackFst r b).toLinearMap.range, s • y = 0) :=
  perfectoidIdeal_ker_coker_annihilated_of_isPullback hR
    (AlgHom.pullbackFst r b) (AlgHom.pullbackSnd r b) r b
    (algHom_isPullback_pullback r b) hC g hg

end SerrePositivity
