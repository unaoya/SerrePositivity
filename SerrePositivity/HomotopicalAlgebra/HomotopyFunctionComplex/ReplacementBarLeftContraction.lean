module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ReplacementBarComparisonSpan
public import SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeBarSpanContraction

/-! # The chosen left comparison leg has an actual simplicial homotopy inverse

This contracts the whole auxiliary diagonal. It does not assume a model
structure on the larger simplicial-set universe or assert the final small descent.
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.HomotopyFunctionComplex.ReplacementMapping
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

abbrev auxiliaryLeftHomotopy (X : Index C) :
    SSet.Homotopy (𝟙 ((auxiliaryMiddle hcof hfib).obj X))
      ((auxiliaryLeft hcof hfib).app X ≫ auxiliarySection hcof hfib X) :=
  SimplicialModel.BarConstruction.spanLeftHomotopy (projection (C := C))
    (uncurried hcof hfib) X

/-- The same actual section and all-degree homotopy witness the left inverse data. -/
theorem auxiliaryLeft_has_homotopyInverse (X : Index C) :
    ∃ s : SSet.uliftFunctor.{max u v, v}.obj ((uncurried hcof hfib).obj X) ⟶
      (auxiliaryMiddle hcof hfib).obj X,
      s ≫ (auxiliaryLeft hcof hfib).app X = 𝟙 _ ∧
        Nonempty (SSet.Homotopy (𝟙 _) ((auxiliaryLeft hcof hfib).app X ≫ s)) :=
  ⟨auxiliarySection hcof hfib X, auxiliarySection_retract hcof hfib X,
    ⟨auxiliaryLeftHomotopy hcof hfib X⟩⟩

end SerrePositivity.HomotopyFunctionComplex.ReplacementMapping
