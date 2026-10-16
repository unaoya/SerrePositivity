module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.SimplexInverseMatching

/-! # Objectwise trivial fibrations between inverse-inverting simplex diagrams

Both value diagrams can vary. Empty matching boundaries recover the
actual objectwise arrow, while nonempty boundaries give an isomorphism.
This permits relative coherent boundary data, not only a constant point.
-/

@[expose] public section
universe w v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy

namespace SerrePositivity.SimplicialModel.SimplexNaturalMatching
variable (X : SSet.{w}) [ModelCategory SSet.{v}]
  (A B : X.Elementsᵒᵖ ⥤ SSet.{v}) (p : A ⟶ B)
  (hA : ∀ {a b : X.Elementsᵒᵖ} (f : a ⟶ b),
    (elementsDirect (direct := simplexInverse.op) X).op f → IsIso (A.map f))
  (hB : ∀ {a b : X.Elementsᵒᵖ} (f : a ⟶ b),
    (elementsDirect (direct := simplexInverse.op) X).op f → IsIso (B.map f))
  (hp : ∀ s, trivialFibrations SSet.{v} (p.app s))

include hA hB hp in
lemma relativeMatching_trivialFibration (s : X.Elementsᵒᵖ) :
    trivialFibrations SSet.{v} (relativeMatchingMap (SimplexIndexFinite.reedy X) s p) := by
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
    apply ((trivialFibrations SSet.{v}).arrow_iso_iff hi).mpr
    change trivialFibrations SSet.{v}
      ((matchingComparison (SimplexIndexFinite.reedy X) s).app A)
    exact (trivialFibrations SSet.{v}).of_isIso _
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
    apply ((trivialFibrations SSet.{v}).arrow_iso_iff hi).mpr
    change trivialFibrations SSet.{v} (p.app s)
    exact hp s

include hA hB hp in
lemma reedyRight : Reedy.reedyRight (SimplexIndexFinite.reedy X)
    (trivialFibrations SSet.{v}) p :=
  fun s => relativeMatching_trivialFibration X A B p hA hB hp s

end SerrePositivity.SimplicialModel.SimplexNaturalMatching
