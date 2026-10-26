module
public import SerrePositivity.DifferentialGraded.Complexes.KProjectiveHom
public import SerrePositivity.DifferentialGraded.Complexes.Closed
public import Mathlib.CategoryTheory.Adjunction.Unique

/-! 全次数内部 Hom の随伴一意性による K-projective 複体の tensor 閉性。 -/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A]

lemma complexTensor_isKProjective (P Q : Complex A) [P.IsKProjective] [Q.IsKProjective] :
    (P ⊗ Q).IsKProjective := by
  apply isKProjective_of_homComplex_acyclic A
  intro N hN
  let e := (ihom.adjunction (P ⊗ Q)).rightAdjointUniq
    (tensorClosed (complexClosed P) (complexClosed Q)).adj
  exact cochainAcyclic_of_iso
    (homComplex_acyclic_of_isKProjective A Q (homComplex A P N)
      (homComplex_acyclic_of_isKProjective A P N hN)) (e.app N).symm

end SerrePositivity.DifferentialGraded
