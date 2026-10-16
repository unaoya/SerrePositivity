module

public import SerrePositivity.HomologicalAlgebra.TorAcyclicBaseChangeResolution
public import SerrePositivity.HomologicalAlgebra.TorAlgebraScalarComparison
public import SerrePositivity.HomologicalAlgebra.BaseChangeEquivalence

/-! # Coefficient scalar actions under Tor-acyclic change of base

The comparison is linear over the final coefficient algebra, so it preserves
all its scalar actions, including those coming from an almost ideal.
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {R B C : Type u} [CommRing R] [CommRing B] [CommRing C]
  [Algebra R B] [Algebra B C] [Algebra R C] [IsScalarTower R B C]

/-- Tor-acyclic scalar extension gives an actual C-linear Tor comparison. -/
def torAlgebraAcyclicBaseChangeIso (M : ModuleCat.{u} R)
    (hM : scalarExtensionTorVanishing (algebraMap R B) M) (i : ℕ) :
    ((ModuleCat.extendScalars (algebraMap R C)).leftDerived i).obj M ≅
      ((ModuleCat.extendScalars (algebraMap B C)).leftDerived i).obj
        ((ModuleCat.extendScalars (algebraMap R B)).obj M) := by
  let P := projectiveResolution M
  let K := extRes P
  let hK := isResolutionOf_extRes P
  let hKB := isResolutionOf_baseChange_of_torVanishing (algebraMap R B) M hK hM
  let eA := torIsoCochain (algebraMap R C) hK i
  let eB := torIsoCochain (algebraMap B C) hKB i
  have he : (algebraMap B C).comp (algebraMap R B) = algebraMap R C :=
    (IsScalarTower.algebraMap_eq R B C).symm
  let e : baseChange (algebraMap B C) (baseChange (algebraMap R B) K) ≅
      baseChange (algebraMap R C) K := by
    rw [← he]
    exact baseChangeCompIso (algebraMap R B) (algebraMap B C) K
  exact eA ≪≫ ((HomologicalComplex.homologyFunctor (ModuleCat C) (.up ℤ) (-(i : ℤ))).mapIso e).symm
    ≪≫ eB.symm

/-- The original coefficient scalar actions vanish on exactly the same tests. -/
lemma torCoefficientScalarEndomorphism_acyclicBaseChange_eq_zero_iff (M : ModuleCat.{u} R)
    (hM : scalarExtensionTorVanishing (algebraMap R B) M) (i : ℕ) (c : C) :
    torCoefficientScalarEndomorphism C M i c = 0 ↔
      torCoefficientScalarEndomorphism C ((ModuleCat.extendScalars (algebraMap R B)).obj M) i c = 0 := by
  rw [torAlgebraComparison_scalar_eq_zero_iff, torAlgebraComparison_scalar_eq_zero_iff]
  let e := torAlgebraAcyclicBaseChangeIso (C := C) M hM i
  have he : (c • 𝟙 _) ≫ e.hom = e.hom ≫ (c • 𝟙 _) := by simp
  constructor
  · intro h
    apply (cancel_epi e.hom).mp
    rw [← he, h, zero_comp, comp_zero]
  · intro h
    apply (cancel_mono e.hom).mp
    rw [he, h, comp_zero, zero_comp]

/-- The actual restricted scalar module has the original algebra action on its carrier. -/
def baseChangeScalarAlgebraEquiv : baseChangeScalarModule (algebraMap R B) ≃ₗ[R] B :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun r b => (Algebra.smul_def r (show B from b)).symm }

/-- Flatness supplies acyclicity for every test module, with the actual restricted scalar ring. -/
lemma scalarExtensionTorVanishing_of_flat_algebra [Module.Flat R B] (M : ModuleCat.{u} R) :
    scalarExtensionTorVanishing (algebraMap R B) M := by
  let e := baseChangeScalarAlgebraEquiv (R := R) (B := B)
  have := Module.Flat.of_linearEquiv e
  intro i hi
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi)
  have := torModule_subsingleton_of_flat (R := R)
    (baseChangeScalarModule (algebraMap R B)) M j
  exact ModuleCat.isZero_of_subsingleton _


end SerrePositivity
