module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ReplacementBarLeftContraction
public import SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeBarAnodyneComparison

/-! # Natural anodyne-localized comparison for the actual auxiliary left bar leg -/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.ReplacementMapping
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

/-- No model on SSet[max(u,v)] is an input to this comparison of whole diagrams. -/
abbrev auxiliaryLeftAnodyneIso :
    auxiliaryMiddle (C := C) hcof hfib ⋙ AnodyneHomotopy.anodyneQ ≅
      (uncurried hcof hfib ⋙ SSet.uliftFunctor.{max u v, v}) ⋙ AnodyneHomotopy.anodyneQ :=
  BarConstruction.spanLeftAnodyneIso (projection (C := C)) (uncurried hcof hfib)

lemma auxiliaryLeftAnodyneIso_hom_app (X : Index C) :
    (auxiliaryLeftAnodyneIso hcof hfib).hom.app X =
      AnodyneHomotopy.anodyneQ.map ((auxiliaryLeft hcof hfib).app X) := rfl

end SerrePositivity.HomotopyFunctionComplex.ReplacementMapping
