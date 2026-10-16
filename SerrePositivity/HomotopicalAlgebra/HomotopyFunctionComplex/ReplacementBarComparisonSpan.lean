module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ReplacementBarCandidate
public import SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeBarSpan

/-! # An actual natural span comparing replacement mapping spaces and the strict auxiliary bar

The small mapping spaces enter by their explicit universe lift. Both legs
are actual natural transformations before localization. Their weak equivalence,
and a final small base functor, remain separate requirements.
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.ReplacementMapping
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

abbrev auxiliaryMiddle : Index C ⥤ SSet.{max u v} :=
  BarConstruction.spanMiddle (projection (C := C)) (uncurried hcof hfib)

abbrev auxiliaryLeft : auxiliaryMiddle (C := C) hcof hfib ⟶
    uncurried hcof hfib ⋙ SSet.uliftFunctor.{max u v, v} :=
  BarConstruction.spanLeft (projection (C := C)) (uncurried hcof hfib)

abbrev auxiliaryRight : auxiliaryMiddle (C := C) hcof hfib ⟶
    projection (C := C) ⋙ auxiliaryBar hcof hfib :=
  BarConstruction.spanRight (projection (C := C)) (uncurried hcof hfib)

abbrev auxiliarySection (X : Index C) :
    SSet.uliftFunctor.{max u v, v}.obj ((uncurried hcof hfib).obj X) ⟶
      (auxiliaryMiddle (C := C) hcof hfib).obj X :=
  BarConstruction.spanSection (projection (C := C)) (uncurried hcof hfib) X

lemma auxiliarySection_retract (X : Index C) :
    auxiliarySection hcof hfib X ≫ (auxiliaryLeft (C := C) hcof hfib).app X = 𝟙 _ :=
  BarConstruction.spanSection_retract (projection (C := C)) (uncurried hcof hfib) X

end SerrePositivity.HomotopyFunctionComplex.ReplacementMapping
