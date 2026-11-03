module
public import SerrePositivity.DifferentialGraded.Complexes.TensorCoproduct

/-! # U10b3a：acyclic複体のu-small直積 -/
@[expose] public section
noncomputable section
universe u w
namespace SerrePositivity.DifferentialGraded.Checks
open CategoryTheory Limits
variable (A : Type u) [CommRing A]
example {J : Type w} [Small.{u} J] (F : J → Complex A) (hF : ∀ j, (F j).Acyclic) :
    (∏ᶜ F).Acyclic := complexProduct_acyclic A F hF
example (F : ℕ → Complex A) (hF : ∀ j, (F j).Acyclic) :
    (∏ᶜ F).Acyclic := complexProduct_acyclic A F hF
example (F : Empty → Complex A) : (∏ᶜ F).Acyclic :=
  complexProduct_acyclic A F (fun j => j.elim)
example {J : Type w} [Small.{u} J] (F : J → Complex A) (n : ℤ) :
    IsLimit (Fan.mk ((∏ᶜ F).X n) (fun j => (Pi.π F j).f n)) :=
  complexProductDegreeIsLimit A F n
end SerrePositivity.DifferentialGraded.Checks

#print axioms SerrePositivity.DifferentialGraded.complexProductDegreeIsLimit
#print axioms SerrePositivity.DifferentialGraded.complexProductDegree_hom_ext
#print axioms SerrePositivity.DifferentialGraded.complexProduct_acyclic
