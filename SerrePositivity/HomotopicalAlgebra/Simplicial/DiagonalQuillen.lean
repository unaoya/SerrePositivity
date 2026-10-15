module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.DiagonalRelativeMatching
public import SerrePositivity.HomotopicalAlgebra.Simplicial.DiagonalCofibrations
public import SerrePositivity.HomotopicalAlgebra.Simplicial.ModelCompatibility

/-! # The diagonal Quillen adjunction and bisimplicial weak equivalences

The right adjoint's relative matching maps are boundary pullback-Homs.
The proved SM7 condition therefore supplies the right Quillen condition.
All bisimplicial sets are Reedy cofibrant, so Brown's lemma proves that
rowwise weak equivalences induce actual diagonal weak equivalences.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy SerrePositivity.Quillen

namespace SerrePositivity.BisimplicialModel
variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

include hcof hfib in
lemma relativeMatching_fibration {Z Y : SSet.{v}} (p : Z ⟶ Y) [Fibration p] (n : ℕ) :
    fibrations SSet.{v} (relativeMatchingMap simplexOp (Opposite.op (SimplexCategory.mk n))
      (internalHomRight.map p)) := by
  have : HasQuillenPullbackHom (MonoidalClosed.internalHom (C := SSet.{v})) :=
    SimplicialModel.simplicial_SM7 hcof hfib
  have hi : Cofibration (SSet.boundary.{v} n).ι := by
    rw [cofibration_iff, hcof]
    infer_instance
  have h := HasQuillenPullbackHom.fibration (SSet.boundary.{v} n).ι p
    (boundaryPullbackHom p n) hi inferInstance
  exact ((fibrations SSet.{v}).arrow_iso_iff (relativeMatchingArrowIso p n)).mpr
    (mem_fibrations (boundaryPullbackHom p n).π)

include hcof hfib in
lemma relativeMatching_weakEquivalence {Z Y : SSet.{v}} (p : Z ⟶ Y)
    [Fibration p] [WeakEquivalence p] (n : ℕ) :
    weakEquivalences SSet.{v} (relativeMatchingMap simplexOp (Opposite.op (SimplexCategory.mk n))
      (internalHomRight.map p)) := by
  have : HasQuillenPullbackHom (MonoidalClosed.internalHom (C := SSet.{v})) :=
    SimplicialModel.simplicial_SM7 hcof hfib
  have hi : Cofibration (SSet.boundary.{v} n).ι := by
    rw [cofibration_iff, hcof]
    infer_instance
  have h := HasQuillenPullbackHom.weakEquivalence (SSet.boundary.{v} n).ι p
    (boundaryPullbackHom p n) hi inferInstance (Or.inr inferInstance)
  exact ((weakEquivalences SSet.{v}).arrow_iso_iff (relativeMatchingArrowIso p n)).mpr
    (mem_weakEquivalences (boundaryPullbackHom p n).π)

include hcof hfib in
lemma internalHomRight_isRightQuillen :
    let := simplexOpModelCategory SSet.{v}; IsRightQuillen internalHomRight.{v} := by
  let := simplexOpModelCategory SSet.{v}
  constructor
  · intro Z Y p hp j
    have : Fibration p := ⟨hp⟩
    induction j using Opposite.rec with | _ j =>
      induction j using SimplexCategory.rec with | _ n =>
        exact relativeMatching_fibration hcof hfib p n
  · intro Z Y p hp
    have : Fibration p := ⟨hp.1⟩
    have : WeakEquivalence p := ⟨hp.2⟩
    apply (reedyRight_trivialFibrations_iff simplexOp (internalHomRight.map p)).mp
    intro j
    induction j using Opposite.rec with | _ j =>
      induction j using SimplexCategory.rec with | _ n =>
        exact ⟨relativeMatching_fibration hcof hfib p n,
          relativeMatching_weakEquivalence hcof hfib p n⟩

include hcof hfib in
lemma diagonal_isLeftQuillen :
    let := simplexOpModelCategory SSet.{v}; IsLeftQuillen diagonal.{v} := by
  let := simplexOpModelCategory SSet.{v}
  have : IsRightQuillen internalHomRight.{v} := internalHomRight_isRightQuillen hcof hfib
  exact (isLeftQuillen_iff_isRightQuillen diagonalInternalHomAdjunction).mpr inferInstance

include hcof hfib in
/-- Every rowwise weak equivalence of bisimplicial sets is a diagonal weak equivalence. -/
lemma diagonal_map_weakEquivalence {B B' : SimplexCategoryᵒᵖ ⥤ SSet.{v}} (f : B ⟶ B')
    (hf : ∀ n, weakEquivalences SSet.{v} (f.app n)) :
    weakEquivalences SSet.{v} (diagonal.map f) :=
  diagonal_map_weakEquivalence_of_isLeftQuillen hcof (diagonal_isLeftQuillen hcof hfib) f hf

end SerrePositivity.BisimplicialModel
