module

public import SerrePositivity.IntersectionMultiplicity.ResolutionEvaluation
public import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence

/-!
# Ordinary Euler evaluation and twisting

A semilinear bijection over a surjective ring map preserves module length.
In particular scalar restriction along a ring automorphism preserves lengths
and the ordinary Euler evaluation of any complex.
-/

public section

universe u

open CategoryTheory

namespace SerrePositivity

variable {R S : Type u} [CommRing R] [CommRing S]

/-- Length is invariant under a semilinear bijection when scalars map
surjectively. This is an isomorphism of the submodule lattices. -/
lemma length_eq_of_semilinear_bijective (φ : R →+* S) (hφ : Function.Surjective φ)
    {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
    (f : M →ₛₗ[φ] N) (hf : Function.Bijective f) : Module.length R M = Module.length S N := by
  have : RingHomSurjective φ := ⟨hφ⟩
  rw [Module.length, Module.length, WithBot.unbot_inj,
    Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComapOfBijective f hf)]

/-- Restricting scalars along a ring automorphism preserves length. -/
lemma length_restrictScalars_equiv (σ : R ≃+* R) (M : ModuleCat.{u} R) :
    Module.length R ((ModuleCat.restrictScalars σ.toRingHom).obj M) = Module.length R M := by
  let f : (ModuleCat.restrictScalars σ.toRingHom).obj M →ₛₗ[σ.toRingHom] M :=
    { toFun := id, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
  exact length_eq_of_semilinear_bijective σ.toRingHom σ.surjective f Function.bijective_id

/-- Ordinary Euler evaluation is invariant under scalar restriction by
an automorphism, without hypotheses on finite length or boundedness. -/
lemma chiOrd_restrictScalars_equiv (σ : R ≃+* R)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    chiOrd (((ModuleCat.restrictScalars σ.toRingHom).mapHomologicalComplex _).obj P) =
      chiOrd P := by
  let F := ModuleCat.restrictScalars.{u} σ.toRingHom
  have : F.IsEquivalence := inferInstance
  unfold chiOrd
  congr 1
  funext i
  let e : ((F.mapHomologicalComplex _).obj P).homology i ≅ F.obj (P.homology i) :=
    (P.sc i).mapHomologyIso F
  rw [e.toLinearEquiv.length_eq, length_restrictScalars_equiv]

/-- Every group twist has the same ordinary Euler evaluation. -/
lemma chiOrd_twist {G : Type u} [Group G] [MulSemiringAction G R]
    (g : G) (P : CochainComplex (ModuleCat.{u} R) ℤ) : chiOrd (twist g P) = chiOrd P :=
  chiOrd_restrictScalars_equiv (MulSemiringAction.toRingEquiv G R g) P

end SerrePositivity
