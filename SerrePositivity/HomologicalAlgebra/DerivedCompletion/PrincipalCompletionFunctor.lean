module
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ScalarRestriction

/-! # Principal completion under ring maps and ring equivalences

The source and target are the original Koszul-completion H⁰ rings. Their units
are preserved; no scalar regularity or bounded-torsion assumption is required.
-/
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
variable {R S : Type u} [CommRing R] [CommRing S]

/-- The actual completion is complete for the action of its original ring unit. -/
lemma principalCompletion_isModuleComplete_unit (a : R) :
    letI := principalCompletionCommRing R a
    letI := (principalCompletionUnitRingHom R a).toAlgebra
    letI : Module R (PrincipalCompletionH0 R a) := Algebra.toModule
    IsModuleComplete R a (ModuleCat.of R (PrincipalCompletionH0 R a)) := by
  letI := principalCompletionCommRing R a
  letI := principalCompletionAlgebra R a
  have h := principalCompletionH0_isModuleComplete R a
  rw [isModuleComplete_iff_recurrence_bijective] at h ⊢
  convert h using 1
  funext x n
  exact congrArg (fun z : PrincipalCompletionH0 R a => x n - z)
    ((principalCompletionH0_isCompleteModuleReflection R a).mul_scalar_unit a (x (n + 1)))

/-- Completeness after restricting through the original target completion unit. -/
lemma principalCompletion_isModuleComplete_comp
    (φ : R →+* S) (a : R) (b : S) (hab : φ a = b) :
    letI := principalCompletionCommRing S b
    letI := ((principalCompletionUnitRingHom S b).comp φ).toAlgebra
    letI : Module R (PrincipalCompletionH0 S b) := Algebra.toModule
    IsModuleComplete R a (ModuleCat.of R (PrincipalCompletionH0 S b)) := by
  letI := principalCompletionCommRing S b
  apply (isModuleComplete_ringHom_comp_iff R S _ φ
    (principalCompletionUnitRingHom S b) a).mp
  rw [hab]
  exact principalCompletion_isModuleComplete_unit b

/-- Transport the original principal completion along a ring map carrying a to b. -/
def principalCompletionMap (φ : R →+* S) (a : R) (b : S) (hab : φ a = b) :
    letI := principalCompletionCommRing R a
    letI := principalCompletionCommRing S b
    PrincipalCompletionH0 R a →+* PrincipalCompletionH0 S b := by
  letI := principalCompletionCommRing R a
  letI := principalCompletionCommRing S b
  exact (principalCompletion_existsUnique_ringHom R a _
    ((principalCompletionUnitRingHom S b).comp φ)
    (principalCompletion_isModuleComplete_comp φ a b hab)).choose

/-- The induced map retains the original completion-unit square. -/
lemma principalCompletionMap_comp (φ : R →+* S) (a : R) (b : S) (hab : φ a = b) :
    letI := principalCompletionCommRing R a
    letI := principalCompletionCommRing S b
    (principalCompletionMap φ a b hab).comp (principalCompletionUnitRingHom R a) =
      (principalCompletionUnitRingHom S b).comp φ := by
  letI := principalCompletionCommRing R a
  letI := principalCompletionCommRing S b
  exact (principalCompletion_existsUnique_ringHom R a _
    ((principalCompletionUnitRingHom S b).comp φ)
    (principalCompletion_isModuleComplete_comp φ a b hab)).choose_spec.1

/-- Ring equivalences induce ring equivalences of the actual principal completions. -/
def principalCompletionRingEquiv (e : R ≃+* S) (a : R) (b : S) (hab : e a = b) :
    letI := principalCompletionCommRing R a
    letI := principalCompletionCommRing S b
    PrincipalCompletionH0 R a ≃+* PrincipalCompletionH0 S b := by
  letI := principalCompletionCommRing R a
  letI := principalCompletionCommRing S b
  have hba : e.symm b = a := by rw [← hab, e.symm_apply_apply]
  let F := principalCompletionMap e.toRingHom a b hab
  let G := principalCompletionMap e.symm.toRingHom b a hba
  have hGF : (G.comp F).comp (principalCompletionUnitRingHom R a) =
      principalCompletionUnitRingHom R a := by
    rw [RingHom.comp_assoc, principalCompletionMap_comp, ← RingHom.comp_assoc,
      principalCompletionMap_comp]
    ext x
    simp
  have hFG : (F.comp G).comp (principalCompletionUnitRingHom S b) =
      principalCompletionUnitRingHom S b := by
    rw [RingHom.comp_assoc, principalCompletionMap_comp, ← RingHom.comp_assoc,
      principalCompletionMap_comp]
    ext x
    simp
  have hGFid : G.comp F = RingHom.id _ :=
    (principalCompletion_existsUnique_ringHom R a _ (principalCompletionUnitRingHom R a)
      (principalCompletion_isModuleComplete_unit a)).unique hGF (RingHom.id_comp _)
  have hFGid : F.comp G = RingHom.id _ :=
    (principalCompletion_existsUnique_ringHom S b _ (principalCompletionUnitRingHom S b)
      (principalCompletion_isModuleComplete_unit b)).unique hFG (RingHom.id_comp _)
  exact
    { F with
      invFun := G
      left_inv := fun x => RingHom.congr_fun hGFid x
      right_inv := fun x => RingHom.congr_fun hFGid x }

/-- The equivalence uses the same original ring map on every unit representative. -/
@[simp] lemma principalCompletionRingEquiv_unit
    (e : R ≃+* S) (a : R) (b : S) (hab : e a = b) (x : R) :
    letI := principalCompletionCommRing R a
    letI := principalCompletionCommRing S b
    principalCompletionRingEquiv e a b hab (principalCompletionUnitRingHom R a x) =
      principalCompletionUnitRingHom S b (e x) :=
  RingHom.congr_fun (principalCompletionMap_comp e.toRingHom a b hab) x

end SerrePositivity.DerivedCompletion
