module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.SimplexNaturalMatching

/-! # Matching lifting from objectwise right lifting against all monomorphisms

This argument uses finite matching calculations, with no model structure
in the value universe. It applies to large auxiliary parameter spaces.
-/

@[expose] public section
universe w v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy

namespace SerrePositivity.SimplicialModel.SimplexMonomorphismLifting
variable (X : SSet.{w}) (A B : X.Elementsᵒᵖ ⥤ SSet.{v}) (p : A ⟶ B)
  (hA : ∀ {a b : X.Elementsᵒᵖ} (f : a ⟶ b),
    (elementsDirect (direct := simplexInverse.op) X).op f → IsIso (A.map f))
  (hB : ∀ {a b : X.Elementsᵒᵖ} (f : a ⟶ b),
    (elementsDirect (direct := simplexInverse.op) X).op f → IsIso (B.map f))
  (hp : ∀ s, (MorphismProperty.monomorphisms SSet.{v}).rlp (p.app s))

include hA hB hp in
lemma relativeMatching_rightLifting (s : X.Elementsᵒᵖ) :
    (MorphismProperty.monomorphisms SSet.{v}).rlp
      (relativeMatchingMap (SimplexIndexFinite.reedy X) s p) := by
  classical
  by_cases h : Nonempty (SimplexMatchingTerminal.Index X s)
  · have : Nonempty (SimplexMatchingTerminal.Index X s) := h
    have : IsIso ((matchingComparison (SimplexIndexFinite.reedy X) s).app A) :=
      SimplexMatchingTerminal.matchingComparison_isIso X s A hA
    have : IsIso ((matchingComparison (SimplexIndexFinite.reedy X) s).app B) :=
      SimplexMatchingTerminal.matchingComparison_isIso X s B hB
    have hi : Arrow.mk (relativeMatchingMap (SimplexIndexFinite.reedy X) s p) ≅
        Arrow.mk ((matchingComparison (SimplexIndexFinite.reedy X) s).app A) :=
      Arrow.isoMk (Iso.refl _)
        (asIso (pullback.snd ((matchingComparison (SimplexIndexFinite.reedy X) s).app B)
          ((matchingEvaluation (SimplexIndexFinite.reedy X) s).map p))) (by
            change (𝟙 _) ≫ _ = pullback.lift _ _ _ ≫ pullback.snd _ _
            rw [Category.id_comp, pullback.lift_snd]
            rfl)
    apply (((MorphismProperty.monomorphisms SSet.{v}).rlp).arrow_iso_iff hi).mpr
    change (MorphismProperty.monomorphisms SSet.{v}).rlp
      ((matchingComparison (SimplexIndexFinite.reedy X) s).app A)
    exact (MorphismProperty.monomorphisms SSet.{v}).rlp_of_isIso _
  · have : IsEmpty (SimplexMatchingTerminal.Index X s) := not_nonempty_iff.mp h
    have : IsIso ((matchingEvaluation (SimplexIndexFinite.reedy X) s).map p) :=
      isIso_of_isTerminal (SimplexInverseMatching.emptyMatchingTerminal X s A)
        (SimplexInverseMatching.emptyMatchingTerminal X s B) _
    have hi : Arrow.mk (relativeMatchingMap (SimplexIndexFinite.reedy X) s p) ≅
        Arrow.mk (p.app s) := Arrow.isoMk (Iso.refl _)
          (asIso (pullback.fst ((matchingComparison (SimplexIndexFinite.reedy X) s).app B)
            ((matchingEvaluation (SimplexIndexFinite.reedy X) s).map p))) (by
              change (𝟙 _) ≫ _ = pullback.lift _ _ _ ≫ pullback.fst _ _
              rw [Category.id_comp, pullback.lift_fst]
              rfl)
    apply (((MorphismProperty.monomorphisms SSet.{v}).rlp).arrow_iso_iff hi).mpr
    change (MorphismProperty.monomorphisms SSet.{v}).rlp (p.app s)
    exact hp s

include hA hB hp in
lemma reedyRight : Reedy.reedyRight (SimplexIndexFinite.reedy X)
    ((MorphismProperty.monomorphisms SSet.{v}).rlp) p :=
  fun s => relativeMatching_rightLifting X A B p hA hB hp s

end SerrePositivity.SimplicialModel.SimplexMonomorphismLifting
