module
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PrincipalCompletionFunctor
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletedTensorH0Comparison
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PairZeroCompletion
public import SerrePositivity.CommutativeAlgebra.TensorRingEquiv

/-! # Transport the actual completed tensor H⁰ as a ring via its original ordinary tensor

The principal-completion comparison requires no regularity of p on the ordinary
tensor. It retains the original completed tensor ring and completion unit.
-/
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (p : ℕ) (S T : Type u)
    [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]

/-- The actual completed tensor H⁰ is the principal completion of the ordinary tensor,
including when the ordinary tensor has unbounded p-power torsion. -/
def completedTensorH0PrincipalRingEquiv :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    letI := principalCompletionCommRing (S ⊗[R] T) (p : S ⊗[R] T)
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveCompletedTensorAlgebra R (p : R) S T).X.obj ≃+*
        PrincipalCompletionH0 (S ⊗[R] T) (p : S ⊗[R] T) := by
  letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  letI := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  letI := pdCompletionCommRing (S ⊗[R] T) p 0
  letI := pdCompletionBaseAlgebra R (S ⊗[R] T) p 0
  letI := pairCompletionAlgebra (S ⊗[R] T) (p : S ⊗[R] T) 0
  letI := principalCompletionCommRing (S ⊗[R] T) (p : S ⊗[R] T)
  letI := principalCompletionAlgebra (S ⊗[R] T) (p : S ⊗[R] T)
  exact (completedTensorH0PDAlgEquiv R p S T).toRingEquiv.trans
    (pairCompletionZeroPrincipalAlgEquiv (S ⊗[R] T) (p : S ⊗[R] T)).toRingEquiv

/-- The comparison preserves the original algebra completion unit on every H⁰ class. -/
lemma completedTensorH0PrincipalRingEquiv_unit
    (x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveDerivedTensorAlgebra (R := R) S T).X.obj) :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    letI := principalCompletionCommRing (S ⊗[R] T) (p : S ⊗[R] T)
    completedTensorH0PrincipalRingEquiv R p S T
      (derivedH0AlgMap (boundedAboveCompletionAlgebraUnit R (p : R)
        (boundedAboveDerivedTensorAlgebra (R := R) S T)) x) =
      principalCompletionUnitRingHom (S ⊗[R] T) (p : S ⊗[R] T)
        (derivedTensorH0AlgEquiv S T x) := by
  letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  letI := derivedH0Algebra (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  letI := pdCompletionCommRing (S ⊗[R] T) p 0
  letI := pdCompletionBaseAlgebra R (S ⊗[R] T) p 0
  letI := pairCompletionAlgebra (S ⊗[R] T) (p : S ⊗[R] T) 0
  letI := principalCompletionCommRing (S ⊗[R] T) (p : S ⊗[R] T)
  letI := principalCompletionAlgebra (S ⊗[R] T) (p : S ⊗[R] T)
  change pairCompletionZeroPrincipalAlgEquiv (S ⊗[R] T) (p : S ⊗[R] T)
    (completedTensorH0PDAlgEquiv R p S T _) = _
  rw [completedTensorH0PDAlgEquiv_unit]
  exact pairCompletionZeroPrincipalAlgEquiv_unit _ _ _

variable (R' : Type u) [CommRing R'] (S' T' : Type u)
    [CommRing S'] [CommRing T'] [Algebra R' S'] [Algebra R' T']

/-- An ordinary tensor ring equivalence induces an equivalence of the original
completed tensor H⁰ rings, even across a change of base ring. -/
def completedTensorH0RingEquivOfTensorRingEquiv
    (e : (S ⊗[R] T) ≃+* (S' ⊗[R'] T')) :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R' (p : R') S' T')
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
        (boundedAboveCompletedTensorAlgebra R (p : R) S T).X.obj ≃+*
      (DerivedCategory.homologyFunctor (ModuleCat R') 0).obj
        (boundedAboveCompletedTensorAlgebra R' (p : R') S' T').X.obj := by
  letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R' (p : R') S' T')
  letI := principalCompletionCommRing (S ⊗[R] T) (p : S ⊗[R] T)
  letI := principalCompletionCommRing (S' ⊗[R'] T') (p : S' ⊗[R'] T')
  exact (completedTensorH0PrincipalRingEquiv R p S T).trans
    ((principalCompletionRingEquiv e (p : S ⊗[R] T) (p : S' ⊗[R'] T')
      (map_natCast e p)).trans (completedTensorH0PrincipalRingEquiv R' p S' T').symm)

/-- The transport carries the original completion unit to the original target unit. -/
lemma completedTensorH0RingEquivOfTensorRingEquiv_unit
    (e : (S ⊗[R] T) ≃+* (S' ⊗[R'] T'))
    (x : (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      (boundedAboveDerivedTensorAlgebra (R := R) S T).X.obj) :
    letI := derivedH0CommRing (boundedAboveDerivedTensorAlgebra (R := R') S' T')
    letI := derivedH0Algebra (boundedAboveDerivedTensorAlgebra (R := R') S' T')
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R' (p : R') S' T')
    completedTensorH0RingEquivOfTensorRingEquiv R p S T R' S' T' e
      (derivedH0AlgMap (boundedAboveCompletionAlgebraUnit R (p : R)
        (boundedAboveDerivedTensorAlgebra (R := R) S T)) x) =
      derivedH0AlgMap (boundedAboveCompletionAlgebraUnit R' (p : R')
        (boundedAboveDerivedTensorAlgebra (R := R') S' T'))
        ((derivedTensorH0AlgEquiv S' T').symm (e (derivedTensorH0AlgEquiv S T x))) := by
  letI := derivedH0CommRing (boundedAboveDerivedTensorAlgebra (R := R') S' T')
  letI := derivedH0Algebra (boundedAboveDerivedTensorAlgebra (R := R') S' T')
  letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
  letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R' (p : R') S' T')
  letI := principalCompletionCommRing (S ⊗[R] T) (p : S ⊗[R] T)
  letI := principalCompletionCommRing (S' ⊗[R'] T') (p : S' ⊗[R'] T')
  apply (completedTensorH0PrincipalRingEquiv R' p S' T').injective
  change completedTensorH0PrincipalRingEquiv R' p S' T'
      ((completedTensorH0PrincipalRingEquiv R' p S' T').symm
        (principalCompletionRingEquiv e (p : S ⊗[R] T) (p : S' ⊗[R'] T')
          (map_natCast e p) (completedTensorH0PrincipalRingEquiv R p S T _))) = _
  rw [RingEquiv.apply_symm_apply, completedTensorH0PrincipalRingEquiv_unit,
    principalCompletionRingEquiv_unit, completedTensorH0PrincipalRingEquiv_unit,
    AlgEquiv.apply_symm_apply]

/-- Compatible base and factor presentations identify the actual completed H⁰ rings. -/
def completedTensorH0RingEquivOfPresentations
    (e : R ≃+* R') (f : S ≃+* S') (g : T ≃+* T')
    (hf : ∀ r, f (algebraMap R S r) = algebraMap R' S' (e r))
    (hg : ∀ r, g (algebraMap R T r) = algebraMap R' T' (e r)) :
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R (p : R) S T)
    letI := derivedH0CommRing (boundedAboveCompletedTensorAlgebra R' (p : R') S' T')
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
        (boundedAboveCompletedTensorAlgebra R (p : R) S T).X.obj ≃+*
      (DerivedCategory.homologyFunctor (ModuleCat R') 0).obj
        (boundedAboveCompletedTensorAlgebra R' (p : R') S' T').X.obj :=
  completedTensorH0RingEquivOfTensorRingEquiv R p S T R' S' T'
    (tensorRingEquivOfCompatibleBase e f g hf hg)

end SerrePositivity.DerivedCompletion
