module

public import SerrePositivity.BhattScholze.Perfectoidization.PerfectoidizationCompletedTensorCompatibility
public import SerrePositivity.BhattScholze.Perfectoidization.PerfectoidizationCompletedBaseChange
public import SerrePositivity.BhattScholze.Semiperfectoid.SemiperfectoidSurjectivity

/-! # The ring form of BS Prop. 8.13 for perfectoid base change

The base and new base are perfectoid. The original algebra is arbitrary once its
ring-perfectoidization is specified. The map out of the original G2 completed
tensor H⁰ and the comparison preserve the new-base action and the original unit.

In particular this applies to p-completely flat perfectoid base change. Flatness
is unnecessary for this H⁰ ring universal property. Discreteness of the original
completed tensor, or comparison with a classical completed tensor, is a separate
input; no unbounded p-torsion case is silently replaced by classical completion.
-/

@[expose] public noncomputable section
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory SerrePositivity.DerivedCompletion
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime] (S A C : Type u)
    [CommRing S] [CommRing A] [CommRing C] [Algebra R S] [Algebra R A] [Algebra R C]
    (hR : IsIntegralPerfectoid R p) (hS : IsIntegralPerfectoid S p)
    (f : A →ₐ[R] C) (hf : IsPerfectoidization p f.toRingHom)
local notation "X" => boundedAboveCompletedTensorAlgebra R (p : R) S A
local notation "Y" => boundedAboveCompletedTensorAlgebra R (p : R) S C
set_option quotPrecheck false in
local notation "HX" => (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (X).X.obj
set_option quotPrecheck false in
local notation "HY" => (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (Y).X.obj

/-- The specified perfectoidization map after actual completed base change. -/
def prop813BaseChangeMap :
    letI := derivedH0CommRing X
    letI := derivedH0CommRing Y
    HX →+* HY := by
  letI := derivedH0CommRing X
  letI := derivedH0CommRing Y
  exact completedTensorPerfectoidLift R p S A _
    (perfectoidizationCompletedBaseChangeMap_isPerfectoidization R p S A C hR hS f hf).1
    (perfectoidizationCompletedBaseChangeMap R p S A C f)

/-- The original ordinary-tensor diagram and actual completion units commute. -/
lemma prop813BaseChangeMap_comp_unit :
    letI := derivedH0CommRing X
    letI := derivedH0CommRing Y
    (prop813BaseChangeMap R p S A C hR hS f hf).comp
      (completedTensorPerfectoidizationMap R p S A) =
        perfectoidizationCompletedBaseChangeMap R p S A C f := by
  let := derivedH0CommRing X
  let := derivedH0CommRing Y
  exact completedTensorPerfectoidLift_comp R p S A _ _ _

/-- The base change retains the specified map of the original algebra on every
pure tensor, together with the original new-base coefficient. -/
lemma prop813BaseChangeMap_unit_tmul (b : S) (a : A) :
    letI := derivedH0CommRing X
    letI := derivedH0CommRing Y
    prop813BaseChangeMap R p S A C hR hS f hf
      (completedTensorPerfectoidizationMap R p S A (b ⊗ₜ[R] a)) =
        completedTensorPerfectoidizationMap R p S C (b ⊗ₜ[R] f a) := by
  let := derivedH0CommRing X
  let := derivedH0CommRing Y
  have h := RingHom.congr_fun
    (prop813BaseChangeMap_comp_unit R p S A C hR hS f hf) (b ⊗ₜ[R] a)
  change prop813BaseChangeMap R p S A C hR hS f hf
    (completedTensorPerfectoidizationMap R p S A (b ⊗ₜ[R] a)) =
      completedTensorPerfectoidizationMap R p S C (b ⊗ₜ[R] f a) at h
  exact h

/-- The actual completed base change is a ring-perfectoidization of the original
actual completed tensor H⁰. No finite presentation or torsion bound is added. -/
lemma prop813BaseChangeMap_isPerfectoidization :
    letI := derivedH0CommRing X
    letI := derivedH0CommRing Y
    IsPerfectoidization p (prop813BaseChangeMap R p S A C hR hS f hf) := by
  let := derivedH0CommRing X
  let := derivedH0CommRing Y
  exact completedTensorPerfectoidLift_isPerfectoidization R p S A _ _
    (perfectoidizationCompletedBaseChangeMap_isPerfectoidization R p S A C hR hS f hf)

/-- The map retains the original new-base factor, including its actual H⁰ algebra action. -/
lemma prop813BaseChangeMap_left (b : S) :
    letI := derivedH0CommRing X
    letI := derivedH0Algebra X
    letI := derivedH0CommRing Y
    letI := derivedH0Algebra Y
    prop813BaseChangeMap R p S A C hR hS f hf
      (completedTensorH0LeftAlgHom R (p : R) S A b) =
        completedTensorH0LeftAlgHom R (p : R) S C b := by
  let := derivedH0CommRing X
  let := derivedH0Algebra X
  let := derivedH0CommRing Y
  let := derivedH0Algebra Y
  rw [← completedTensorPerfectoidizationMap_left R p S A b]
  have h := RingHom.congr_fun (prop813BaseChangeMap_comp_unit R p S A C hR hS f hf)
    (b ⊗ₜ[R] (1 : A))
  change prop813BaseChangeMap R p S A C hR hS f hf
    (completedTensorPerfectoidizationMap R p S A (b ⊗ₜ[R] 1)) =
      perfectoidizationCompletedBaseChangeMap R p S A C f (b ⊗ₜ[R] 1) at h
  exact h.trans (perfectoidizationCompletedBaseChangeMap_left R p S A C f b)

/-- BS Prop. 8.13, ring base-change form: comparison with any specified
perfectoidization of the original completed tensor preserves the new base and
the entire completed base-change map. -/
lemma prop813BaseChange_exists_algEquiv (E : Type u) [CommRing E] [Algebra S E] :
    letI := derivedH0CommRing X
    letI := derivedH0Algebra X
    letI := completedTensorH0LeftAlgebra R (p : R) S A
    letI := derivedH0CommRing Y
    letI := derivedH0Algebra Y
    letI := completedTensorH0LeftAlgebra R (p : R) S C
    ∀ (g : HX →ₐ[S] E), IsPerfectoidization p g.toRingHom →
      ∃ e : HY ≃ₐ[S] E,
        e.toRingHom.comp (prop813BaseChangeMap R p S A C hR hS f hf) = g.toRingHom := by
  let := derivedH0CommRing X
  let := derivedH0Algebra X
  let := completedTensorH0LeftAlgebra R (p : R) S A
  let := derivedH0CommRing Y
  let := derivedH0Algebra Y
  let := completedTensorH0LeftAlgebra R (p : R) S C
  intro g hg
  obtain ⟨e, he⟩ :=
    (prop813BaseChangeMap_isPerfectoidization R p S A C hR hS f hf).exists_equiv p hg
  have hc (b : S) : e (algebraMap S HY b) = algebraMap S E b := by
    have hb : prop813BaseChangeMap R p S A C hR hS f hf (algebraMap S HX b) =
        algebraMap S HY b := prop813BaseChangeMap_left R p S A C hR hS f hf b
    rw [← hb]
    exact (RingHom.congr_fun he (algebraMap S HX b)).trans (g.commutes b)
  exact ⟨AlgEquiv.ofRingEquiv (f := e) hc, he⟩

/-- An ordinary-tensor perfectoidization suffices: extend its original unit and
obtain the same new-base algebra comparison on the actual completed source. -/
lemma prop813BaseChange_exists_algEquiv_of_tensor
    (E : Type u) [CommRing E] [Algebra S E]
    (g : S ⊗[R] A →ₐ[S] E) (hg : IsPerfectoidization p g.toRingHom) :
    letI := derivedH0CommRing X
    letI := derivedH0CommRing Y
    letI := derivedH0Algebra Y
    letI := completedTensorH0LeftAlgebra R (p : R) S C
    ∃ e : HY ≃ₐ[S] E,
      e.toRingHom.comp (prop813BaseChangeMap R p S A C hR hS f hf) =
        completedTensorPerfectoidLift R p S A E hg.1 g.toRingHom := by
  let := derivedH0CommRing X
  let := derivedH0CommRing Y
  let := derivedH0Algebra Y
  let := completedTensorH0LeftAlgebra R (p : R) S C
  obtain ⟨e, he⟩ := perfectoidizationCompletedBaseChangeMap_exists_algEquiv
    R p S A C hR hS f hf E g hg
  refine ⟨e, ?_⟩
  apply completedTensorPerfectoid_hom_ext R p S A E hg.1
  rw [RingHom.comp_assoc, prop813BaseChangeMap_comp_unit, he, completedTensorPerfectoidLift_comp]

include hR hS f hf in
/-- The comparison also applies to the actual new-base G2 H⁰ module, with its
original new-base action rather than only the restricted old-base action. -/
lemma prop813BaseChange_exists_linearEquiv (E : Type u) [CommRing E] [Algebra S E] :
    letI := derivedH0CommRing X
    letI := derivedH0Algebra X
    letI := completedTensorH0LeftAlgebra R (p : R) S A
    ∀ (g : HX →ₐ[S] E), IsPerfectoidization p g.toRingHom →
      Nonempty ((DerivedCategory.homologyFunctor (ModuleCat S) 0).obj
        ((boundedAboveDerivedCompletionFunctor S (p : S)).obj
          ((boundedAboveDerivedBaseChange (algebraMap R S)).obj
            (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R C)))).obj ≃ₗ[S] E) := by
  let := derivedH0CommRing X
  let := derivedH0Algebra X
  let := completedTensorH0LeftAlgebra R (p : R) S A
  let := derivedH0CommRing Y
  let := derivedH0Algebra Y
  let := completedTensorH0LeftAlgebra R (p : R) S C
  intro g hg
  obtain ⟨e, _he⟩ := prop813BaseChange_exists_algEquiv R p S A C hR hS f hf E g hg
  have eH := completedBaseChangeTensorH0LinearEquiv R S C (p : R)
  rw [map_natCast] at eH
  exact ⟨eH.trans e.toLinearEquiv⟩

/-- B3 supplies the specified perfectoidization for every perfectoid quotient,
so the base-change theorem does not require a new integral-existence citation. -/
theorem exists_prop813BaseChange_of_perfectoid_quotient
    (hq : Function.Surjective (algebraMap R A)) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra R C) (f : A →ₐ[R] C),
      ∃ hf : IsPerfectoidization p f.toRingHom,
        letI := derivedH0CommRing X
        letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S C)
        IsPerfectoidization p (prop813BaseChangeMap R p S A C hR hS f hf) := by
  obtain ⟨C, hC, f, hf⟩ :=
    exists_perfectoidization_of_perfectoid_surjective_quotient hR (algebraMap R A) hq
  let := hC
  let hRC : Algebra R C := (f.comp (algebraMap R A)).toAlgebra
  let fA : A →ₐ[R] C := { f with commutes' := fun _ => rfl }
  have hfA : IsPerfectoidization p fA.toRingHom := hf
  exact ⟨C, hC, hRC, fA, hfA,
    prop813BaseChangeMap_isPerfectoidization R p S A C hR hS fA hfA⟩

/-- For a derived p-complete quotient, B4 also makes the original specified
perfectoidization surjective. General p-torsion quotients are included. -/
theorem exists_prop813BaseChange_of_semiperfectoid_quotient
    (hq : Function.Surjective (algebraMap R A))
    (hA : IsModuleComplete A (p : A) (ModuleCat.of A A)) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra R C) (f : A →ₐ[R] C),
      ∃ hf : IsPerfectoidization p f.toRingHom,
        Function.Surjective f ∧
          (letI := derivedH0CommRing X
           letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S C)
           IsPerfectoidization p (prop813BaseChangeMap R p S A C hR hS f hf)) := by
  obtain ⟨C, hC, hRC, f, hf, hbase⟩ :=
    exists_prop813BaseChange_of_perfectoid_quotient R p S A hR hS hq
  let := hC
  let := hRC
  exact ⟨C, hC, hRC, f, hf,
    surjective_of_isPerfectoidization_of_semiperfectoid_quotient hR
      (algebraMap R A) hq hA f.toRingHom hf, hbase⟩

end SerrePositivity.BhattScholze
