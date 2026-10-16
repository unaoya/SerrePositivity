module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.OrdinaryBarWordEvaluationOperators

/-! # All free-resolution operator laws on native small word-arrow action families -/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarWordActionOperators
open FreeGeneratorCategories OrdinaryBarFreeResolutionSeed OrdinaryBarChoiceBoundaryGluing
open OrdinaryBarRetractSystem OrdinaryBarWordAction OrdinaryBarWordEvaluationOperators
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (P : SSet.{max u v}) (n : ℕ) {T : SSet.{v}}

lemma family_face (i : Fin (n + 2))
    (j : UniverseLift.obj.{max u v} T ⟶ parameters P n)
    {X Y : degree (D C) (n + 2)}
    (f : UniverseLift.obj.{max u v} T ⟶ hom (C := C) (n + 1) X Y) :
    family hcof hfib P n j (f ≫ WordPresentationSourceMap.mapHomSame
        (FreeGeneratorFaces.fixedFace (D C) (n + 1) i) X Y) =
      family hcof hfib P (n + 1) (j ≫ P ◁ SSet.stdSimplex.δ i) f := by
  ext k x
  have he := congr($(evaluation_face (C := C) hcof hfib P n i k
    (j.app k (ULift.up x.2))).map (f.app k (ULift.up x.2)))
  exact congrArg ULift.down (types_congr_hom he (ULift.up x.1))

lemma family_degeneracy (i : Fin (n + 1))
    (j : UniverseLift.obj.{max u v} T ⟶ parameters P (n + 1))
    {X Y : degree (D C) (n + 1)}
    (f : UniverseLift.obj.{max u v} T ⟶ hom (C := C) n X Y) :
    family hcof hfib P (n + 1) j (f ≫ WordPresentationSourceMap.mapHomSame
        (degeneracyFunctor (D C) n i) X Y) =
      family hcof hfib P n
        (j ≫ P ◁ OrdinaryBarFreeResolutionDegeneracyValues.sigma n i) f := by
  ext k x
  have he := congr($(evaluation_degeneracy (C := C) hcof hfib P n i k
    (j.app k (ULift.up x.2))).map (f.app k (ULift.up x.2)))
  exact congrArg ULift.down (types_congr_hom he (ULift.up x.1))

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarWordActionOperators
