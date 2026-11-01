module
public import SerrePositivity.DifferentialGraded.Quotient.Path.Construction
public import Mathlib.Data.ZMod.Basic

/-! # 明示的dg商のpath添字・内部微分tensor項の受入監査 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory Limits MonoidalCategory
open SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.DGQuotient
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

example (S : Set D) (x y : D) : term A D ([] : Word S) x y = homObject A D x y := rfl
example (S : Set D) (b c : S) : epsilonDegree ([b, c] : Word S) = -2 := by simp
example (S : Set D) (b : S) :
    complexSphere A (-1) ⟶ term A D [b] b.val b.val := epsilonTerm A D b
example (S : Set D) (x y z : D) :
    appendMap A D ([] : Word S) [] x y z = eComp (Complex A) x y z := rfl
example (P Q : Complex A) :
    term A (Complex A) ([] : Word (∅ : Set (Complex A))) P Q = homComplex A P Q := rfl

section
variable [Small.{u} D]
example (S : Set D) : Small.{u} (Word S) := inferInstance
example (x y : D) : homObject A D x y ≅ internalHom A D ∅ x y := emptyHomIso A D x y
example (S : Set D) (x y : D) (T : Complex A) :
    (internalHom A D S x y ⟶ T) ≃ (∀ w : Word S, term A D w x y ⟶ T) := homEquiv A D S x y T
end

example (b : (Set.univ : Set PUnit.{1})) :
    epsilonDegree ([b] : Word (Set.univ : Set PUnit.{1})) = -1 := by simp
example : homObject (ZMod 2) PUnit.{1} PUnit.unit PUnit.unit ≅
    internalHom (ZMod 2) PUnit.{1} ∅ PUnit.unit PUnit.unit :=
  emptyHomIso (ZMod 2) PUnit.{1} PUnit.unit PUnit.unit

#print axioms DGQuotient.epsilonDegree
#print axioms DGQuotient.epsilonDegree_nil
#print axioms DGQuotient.epsilonDegree_cons
#print axioms DGQuotient.epsilonDegree_append
#print axioms DGQuotient.term
#print axioms DGQuotient.term_nil
#print axioms DGQuotient.term_cons
#print axioms DGQuotient.epsilonTerm
#print axioms DGQuotient.wordSmall
#print axioms DGQuotient.ι
#print axioms DGQuotient.originalHom
#print axioms DGQuotient.epsilon
#print axioms DGQuotient.hom_ext
#print axioms DGQuotient.desc
#print axioms DGQuotient.ι_desc
#print axioms DGQuotient.homEquiv
#print axioms DGQuotient.word_empty
#print axioms DGQuotient.emptyHomIso
#print axioms DGQuotient.prependMap
#print axioms DGQuotient.prependMap_nil
#print axioms DGQuotient.appendMap
#print axioms DGQuotient.appendMap_nil_left
#print axioms DGQuotient.appendMap_nil_nil
