module

public import SerrePositivity.HomotopicalAlgebra.Generated.Basic
public import SerrePositivity.HomotopicalAlgebra.Quillen.Adjunction

/-!
# Recognition of generated model structures

The proof uses the small object argument twice and the retract argument to
identify the trivial cofibrations. Acyclicity is a separate, explicit hypothesis.
The result constructs Mathlib's `ModelCategory` on the caller's chosen classes.
-/

@[expose] public section

universe w u v

open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.ModelGeneration

variable {C : Type u} [Category.{v} C]
  [CategoryWithCofibrations C] [CategoryWithFibrations C]
  [CategoryWithWeakEquivalences C]
  [(weakEquivalences C).HasTwoOutOfThreeProperty]

/-- The retract argument is the essential recognition step. Factoring a weak
cofibration through the J-system makes its right factor a trivial fibration. -/
lemma trivialCofibrations_eq_of_recognition (I J : MorphismProperty C)
    [I.HasSmallObjectArgument.{w}] [J.HasSmallObjectArgument.{w}]
    (hI : I.rlp = trivialFibrations C) (hJ : J.rlp = fibrations C)
    (hC : cofibrations C = I.rlp.llp)
    (hacyclic : J.rlp.llp ≤ weakEquivalences C) :
    trivialCofibrations C = J.rlp.llp := by
  apply le_antisymm
  · intro X Y f hf
    let fac := MorphismProperty.factorizationData J.rlp.llp J.rlp f
    have hiW : weakEquivalences C fac.i := hacyclic _ fac.hi
    have hpW : weakEquivalences C fac.p :=
      (weakEquivalences C).of_precomp fac.i fac.p hiW (by simpa using hf.2)
    have hpI : I.rlp fac.p := by
      rw [hI]
      exact ⟨hJ ▸ fac.hp, hpW⟩
    have hfL : I.rlp.llp f := hC ▸ hf.1
    have : HasLiftingProperty f fac.p := hfL _ hpI
    exact MorphismProperty.of_retract (RetractArrow.ofLeftLiftingProperty fac.fac) fac.hi
  · intro X Y f hf
    refine ⟨?_, hacyclic _ hf⟩
    rw [hC]
    apply MorphismProperty.antitone_llp (show I.rlp ≤ J.rlp from ?_) _ hf
    rw [hI, hJ]
    exact fun _ _ _ h ↦ h.1

/-- Recognition theorem with both small-object and acyclicity hypotheses.
Finite limits/colimits are required separately from cofibrant generation. -/
@[instance_reducible]
def modelCategoryOfRecognition (I J : MorphismProperty C)
    [I.HasSmallObjectArgument.{w}] [J.HasSmallObjectArgument.{w}]
    [Limits.HasFiniteLimits C] [Limits.HasFiniteColimits C]
    (hI : I.rlp = trivialFibrations C) (hJ : J.rlp = fibrations C)
    (hC : cofibrations C = I.rlp.llp)
    (hacyclic : J.rlp.llp ≤ weakEquivalences C) : ModelCategory C := by
  have : MorphismProperty.IsWeakFactorizationSystem
      (cofibrations C) (trivialFibrations C) := by
    rw [hC, ← hI]
    infer_instance
  have : MorphismProperty.IsWeakFactorizationSystem
      (trivialCofibrations C) (fibrations C) := by
    rw [trivialCofibrations_eq_of_recognition I J hI hJ hC hacyclic, ← hJ]
    infer_instance
  exact ModelCategory.mk' C

end SerrePositivity.ModelGeneration
