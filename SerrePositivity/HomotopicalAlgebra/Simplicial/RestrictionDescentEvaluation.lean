module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.RestrictionDescentChoices

/-! # The comparison family restricts to the original map over the whole parameter -/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonoidalClosed

namespace SerrePositivity.SimplicialModel.RestrictionDescentChoices

lemma constant_name_family {A K T : SSet.{v}} (h : A ⟶ K)
    (p : T ⟶ SSet.stdSimplex.obj (SimplexCategory.mk 0)) :
    uncurry (p ≫ RelativeChoiceSpace.name h) = fst A T ≫ h := by
  rw [RelativeChoiceSpace.name, ← Category.assoc, uncurry_natural_left]
  dsimp only [curry']
  rw [uncurry_curry]
  have hp : p ≫ RelativeChoiceSpace.pointUnitIso.hom = toUnit T :=
    CartesianMonoidalCategory.isTerminalTensorUnit.hom_ext _ _
  rw [hp]
  rfl

variable {A B K : SSet.{v}} (a : A ⟶ B)
  (ha : IsIso (AnodyneHomotopy.anodyneQ.map a))
  (hK : SSet.modelCategoryQuillen.J.rlp (CategoryTheory.Limits.terminal.from K))

def fixedFamilyComparison {T : SSet.{v}} (h : A ⟶ K) (c : T ⟶ obj a h) :
    SSet.Homotopy (a ▷ T ≫ family a ha hK h c) (fst A T ≫ h) :=
  LargeParameterSquare.changeEndpoints (familyComparison a ha hK h c) rfl
    (by rw [← Category.assoc]; exact constant_name_family h (c ≫ toPoint a h))

end SerrePositivity.SimplicialModel.RestrictionDescentChoices
