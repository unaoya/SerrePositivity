module
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionH0PrincipalComparison
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PDCompletion
public import SerrePositivity.HomologicalAlgebra.DerivedTensorNonpositive

/-! # Original iterated p,d algebra completion H⁰ and actual two-coordinate completion -/
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (p : ℕ) (d : R)
    (A : CommMon (DerivedCategory.Minus (ModuleCat.{u} R))) [A.X.obj.IsLE 0]
set_option quotPrecheck false in
local notation "AP" => (boundedAboveCompletionCommMonFunctor R (p : R)).obj A
set_option quotPrecheck false in
local notation "B" => (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (AP).X.obj
set_option quotPrecheck false in
local notation "C" => (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
  ((boundedAboveCompletionCommMonFunctor R d).obj AP).X.obj
local notation "J" => derivedH0AlgMap (boundedAboveCompletionAlgebraUnit R d AP)
/-- Actual iterated p,d completion has the actual F3 H⁰ algebra of the first H⁰. -/
def iteratedAlgebraCompletionH0PDAlgEquiv :
    letI := derivedH0CommRing AP
    letI := derivedH0Algebra AP
    letI := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R d).obj AP)
    letI := derivedH0Algebra ((boundedAboveCompletionCommMonFunctor R d).obj AP)
    letI := completionH0ScalarAlgebra R d AP
    letI := pdCompletionCommRing B p (algebraMap R B d)
    letI := pdCompletionAlgebra B p (algebraMap R B d)
    C ≃ₐ[B] PDCompletionH0 B p (algebraMap R B d) := by
  letI := derivedH0CommRing AP
  letI := derivedH0Algebra AP
  letI := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R d).obj AP)
  letI := derivedH0Algebra ((boundedAboveCompletionCommMonFunctor R d).obj AP)
  letI := completionH0ScalarAlgebra R d AP
  letI := pdCompletionCommRing B p (algebraMap R B d)
  letI := pdCompletionAlgebra B p (algebraMap R B d)
  let hle : (AP).X.obj.IsLE 0 :=
    boundedAboveDerivedCompletionFunctor_isLE R (p : R) A.X 0 inferInstance
  have hB : IsModuleComplete R (p : R) B :=
    derivedComplexCompletionFunctor_homology_isModuleComplete R (p : R) A.X.obj 0
  have aux (c : B) (hc : algebraMap R B (p : R) = c) :
      letI := pairCompletionCommRing B c (algebraMap R B d)
      letI := pairCompletionAlgebra B c (algebraMap R B d)
      C ≃ₐ[B] PairCompletionH0 B c (algebraMap R B d) := by
    subst c
    exact completionH0PairAlgEquivOfCompleteFirst R d AP (p : R) hB
  exact aux (p : B) (map_natCast (algebraMap R B) p)

/-- The second original completion unit is preserved, with coefficient p unchanged. -/
lemma iteratedAlgebraCompletionH0PDAlgEquiv_unit (x : B) :
    letI := derivedH0CommRing AP
    letI := derivedH0Algebra AP
    letI := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R d).obj AP)
    letI := derivedH0Algebra ((boundedAboveCompletionCommMonFunctor R d).obj AP)
    letI := completionH0ScalarAlgebra R d AP
    letI := pdCompletionCommRing B p (algebraMap R B d)
    letI := pdCompletionAlgebra B p (algebraMap R B d)
    iteratedAlgebraCompletionH0PDAlgEquiv R p d A (J x) =
      pdCompletionUnit B p (algebraMap R B d) x := by
  let := derivedH0CommRing AP
  let := derivedH0Algebra AP
  let := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R d).obj AP)
  let := derivedH0Algebra ((boundedAboveCompletionCommMonFunctor R d).obj AP)
  let := completionH0ScalarAlgebra R d AP
  let := pdCompletionCommRing B p (algebraMap R B d)
  let := pdCompletionAlgebra B p (algebraMap R B d)
  exact (iteratedAlgebraCompletionH0PDAlgEquiv R p d A).commutes x

variable (S T : Type u) [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
local notation "ATP" => boundedAboveCompletedTensorAlgebra R (p : R) S T
set_option quotPrecheck false in
local notation "BT" => (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj (ATP).X.obj
/-- The original completed derived tensor followed by d-completion, as a coefficient algebra. -/
def iteratedCompletedTensorH0PDAlgEquiv :
    letI := derivedH0CommRing ATP
    letI := derivedH0Algebra ATP
    letI := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R d).obj ATP)
    letI := derivedH0Algebra ((boundedAboveCompletionCommMonFunctor R d).obj ATP)
    letI := completionH0ScalarAlgebra R d ATP
    letI := pdCompletionCommRing BT p (algebraMap R BT d)
    letI := pdCompletionAlgebra BT p (algebraMap R BT d)
    (DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
      ((boundedAboveCompletionCommMonFunctor R d).obj ATP).X.obj ≃ₐ[BT]
      PDCompletionH0 BT p (algebraMap R BT d) := by
  letI := derivedH0CommRing ATP
  letI := derivedH0Algebra ATP
  letI := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R d).obj ATP)
  letI := derivedH0Algebra ((boundedAboveCompletionCommMonFunctor R d).obj ATP)
  letI := completionH0ScalarAlgebra R d ATP
  letI := pdCompletionCommRing BT p (algebraMap R BT d)
  letI := pdCompletionAlgebra BT p (algebraMap R BT d)
  let hle : (boundedAboveDerivedTensorAlgebra (R := R) S T).X.obj.IsLE 0 := by
    change ((boundedAboveDerivedTensorModuleFunctor (ModuleCat.of R S)).obj
      (ModuleCat.of R T)).IsLE 0
    infer_instance
  exact iteratedAlgebraCompletionH0PDAlgEquiv R p d
    (boundedAboveDerivedTensorAlgebra (R := R) S T)

/-- In particular the standard image of the original d is retained by this comparison. -/
lemma iteratedCompletedTensorH0PDAlgEquiv_unit (x : BT) :
    letI := derivedH0CommRing ATP
    letI := derivedH0Algebra ATP
    letI := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R d).obj ATP)
    letI := derivedH0Algebra ((boundedAboveCompletionCommMonFunctor R d).obj ATP)
    letI := completionH0ScalarAlgebra R d ATP
    letI := pdCompletionCommRing BT p (algebraMap R BT d)
    letI := pdCompletionAlgebra BT p (algebraMap R BT d)
    iteratedCompletedTensorH0PDAlgEquiv R p d S T
      (derivedH0AlgMap (boundedAboveCompletionAlgebraUnit R d ATP) x) =
        pdCompletionUnit BT p (algebraMap R BT d) x := by
  let := derivedH0CommRing ATP
  let := derivedH0Algebra ATP
  let := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R d).obj ATP)
  let := derivedH0Algebra ((boundedAboveCompletionCommMonFunctor R d).obj ATP)
  let := completionH0ScalarAlgebra R d ATP
  let := pdCompletionCommRing BT p (algebraMap R BT d)
  let := pdCompletionAlgebra BT p (algebraMap R BT d)
  exact (iteratedCompletedTensorH0PDAlgEquiv R p d S T).commutes x

/-- The original base scalar, in particular the original d generator, is preserved. -/
lemma iteratedCompletedTensorH0PDAlgEquiv_algebraMap (r : R) :
    letI := derivedH0CommRing ATP
    letI := derivedH0Algebra ATP
    letI := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R d).obj ATP)
    letI := derivedH0Algebra ((boundedAboveCompletionCommMonFunctor R d).obj ATP)
    letI := completionH0ScalarAlgebra R d ATP
    letI := pdCompletionCommRing BT p (algebraMap R BT d)
    letI := pdCompletionAlgebra BT p (algebraMap R BT d)
    iteratedCompletedTensorH0PDAlgEquiv R p d S T
      (algebraMap R ((DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
        ((boundedAboveCompletionCommMonFunctor R d).obj ATP).X.obj) r) =
      pdCompletionUnit BT p (algebraMap R BT d) (algebraMap R BT r) := by
  let := derivedH0CommRing ATP
  let := derivedH0Algebra ATP
  let := derivedH0CommRing ((boundedAboveCompletionCommMonFunctor R d).obj ATP)
  let := derivedH0Algebra ((boundedAboveCompletionCommMonFunctor R d).obj ATP)
  let := completionH0ScalarAlgebra R d ATP
  let := pdCompletionCommRing BT p (algebraMap R BT d)
  let := pdCompletionAlgebra BT p (algebraMap R BT d)
  have h := iteratedCompletedTensorH0PDAlgEquiv_unit R p d S T (algebraMap R BT r)
  rw [AlgHom.commutes] at h
  exact h

end SerrePositivity.DerivedCompletion
