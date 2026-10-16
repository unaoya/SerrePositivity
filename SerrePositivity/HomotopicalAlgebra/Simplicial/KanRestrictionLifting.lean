module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.HomotopyClassesClosed
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanFibrationLocalizedLifting
public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneLocalizedTensor

/-! # All-monomorphism lifting for restriction along a localized mono equivalence

The tensor comparison and the closed homotopy-class adjunction prove the
covariant tests for the actual restriction fibration. Its strict section
and contraction give all-monomorphism lifting in any value universe.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace SerrePositivity.SimplicialModel.KanRestrictionLifting
variable {A B K : SSet.{v}} (i : A ⟶ B)
  (hi : IsIso (AnodyneHomotopy.anodyneQ.map i))
  (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K))

include hi hK in
lemma post_bijective (X : SSet.{v}) :
    Function.Bijective (HomotopyClasses.post ((MonoidalClosed.pre i).app K) (X := X)) := by
  have ht := KanTestDetection.tests_of_anodyneQ_isIso (i ▷ X)
    (AnodyneHomotopy.whiskerRight_anodyneQ_isIso i hi X) K hK
  constructor
  · intro x y h
    apply (HomotopyClassesClosed.equiv (A := B) (X := X) (K := K)).symm.injective
    apply ht.injective
    change HomotopyClasses.pre (i ▷ X) (HomotopyClassesClosed.uncurryClass x) =
      HomotopyClasses.pre (i ▷ X) (HomotopyClassesClosed.uncurryClass y)
    rw [← HomotopyClassesClosed.uncurryClass_post, ← HomotopyClassesClosed.uncurryClass_post, h]
  · intro y
    obtain ⟨z, hz⟩ := ht.surjective (HomotopyClassesClosed.uncurryClass y)
    refine ⟨HomotopyClassesClosed.curryClass z, ?_⟩
    apply (HomotopyClassesClosed.equiv (A := A) (X := X) (K := K)).symm.injective
    change HomotopyClassesClosed.uncurryClass _ = _
    rw [HomotopyClassesClosed.uncurryClass_post]
    change HomotopyClasses.pre (i ▷ X)
      ((HomotopyClassesClosed.equiv (A := B) (X := X) (K := K)).symm
        (HomotopyClassesClosed.equiv z)) = _
    rw [Equiv.symm_apply_apply]
    exact hz

include hi hK in
lemma all_mono_rlp [Mono i] :
    (MorphismProperty.monomorphisms SSet.{v}).rlp ((MonoidalClosed.pre i).app K) := by
  have : Fibration (terminal.from K) := (SSet.modelCategoryQuillen.fibration_iff _).mpr hK
  have : SSet.KanComplex K := (isFibrant_iff K).mpr inferInstance
  have hp : SSet.modelCategoryQuillen.J.rlp ((MonoidalClosed.pre i).app K) :=
    (SSet.modelCategoryQuillen.fibration_iff _).mp inferInstance
  have hB : SSet.modelCategoryQuillen.J.rlp (terminal.from ((ihom A).obj K)) :=
    (SSet.modelCategoryQuillen.fibration_iff _).mp inferInstance
  exact KanFibrationLocalizedLifting.of_post_tests _ hp hB
    (post_bijective i hi hK _).surjective (post_bijective i hi hK _).injective

include hi hK in
lemma boundary_rlp [Mono i] : SSet.modelCategoryQuillen.I.rlp ((MonoidalClosed.pre i).app K) := by
  rw [← SSet.rlp_monomorphisms]
  exact all_mono_rlp i hi hK

end SerrePositivity.SimplicialModel.KanRestrictionLifting
