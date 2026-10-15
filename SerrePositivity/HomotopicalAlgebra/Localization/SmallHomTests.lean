module

public import SerrePositivity.HomotopicalAlgebra.Localization.Basic
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.SmallHomComparison

/-! # Locality using small-Hom mapping spaces

The original Hom universe and the presentability universe are independent.
Both tests use the same actual source resolution and target replacement.
Their maps are isomorphic after common universe lift, so the proved
universe-change theorem identifies the locality predicates and classes.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.HomotopyFunctionComplex

namespace SerrePositivity.Bousfield
variable {C : Type u} [Category.{v} C] [ModelCategory C] [IsLocallyPresentable.{w} C]
  [ModelCategory SSet.{w}]
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))

abbrev smallMappingTest (Y : C) : MorphismProperty C :=
  MappingTests.test (SmallHomComparison.chosenHom cof fib) (weakEquivalences SSet.{w}) Y

abbrev smallLocalObjects (S : MorphismProperty C) : C → Prop :=
  MappingTests.localObjects (SmallHomComparison.chosenHom cof fib) (weakEquivalences SSet.{w}) S

abbrev smallLocalEquivalences (S : MorphismProperty C) : MorphismProperty C :=
  MappingTests.localEquivalences (SmallHomComparison.chosenHom cof fib)
    (weakEquivalences SSet.{w}) S

variable [ModelCategory SSet.{v}] [ModelCategory SSet.{max v w}]
  (hcofW : cofibrations SSet.{w} = MorphismProperty.monomorphisms _)
  (hfibW : fibrations SSet.{w} = SSet.modelCategoryQuillen.J.{w}.rlp)
  (hcofV : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfibV : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (hcofB : cofibrations SSet.{max v w} = MorphismProperty.monomorphisms _)
  (hfibB : fibrations SSet.{max v w} = SSet.modelCategoryQuillen.J.{max v w}.rlp)

include hcofW hfibW hcofV hfibV hcofB hfibB

lemma smallMappingTest_eq (Y : C) :
    smallMappingTest.{w, v, u} cof fib Y = mappingTest (C := C) cof fib Y := by
  ext X Z f
  exact SimplicialModel.UniverseLift.weakEquivalences_iff_of_liftedArrowIso.{v, w}
    hcofW hfibW hcofB hfibB hcofV hfibV _ _
    (SmallHomComparison.sourceArrowIso (Reedy.cosimplicialResolutionFamily cof).obj
      (fibrantTarget fib) f Y)

lemma smallLocalObjects_eq (S : MorphismProperty C) :
    smallLocalObjects.{w, v, u} cof fib S = localObjects (C := C) cof fib S := by
  funext Y
  change (S ≤ smallMappingTest.{w, v, u} cof fib Y) = (S ≤ mappingTest (C := C) cof fib Y)
  rw [smallMappingTest_eq.{w, v, u} cof fib hcofW hfibW hcofV hfibV hcofB hfibB Y]

lemma smallLocalEquivalences_eq (S : MorphismProperty C) :
    smallLocalEquivalences.{w, v, u} cof fib S = localEquivalences (C := C) cof fib S := by
  ext X Y f
  have ho := smallLocalObjects_eq.{w, v, u} cof fib hcofW hfibW hcofV hfibV hcofB hfibB S
  change (∀ Z, smallLocalObjects.{w, v, u} cof fib S Z → smallMappingTest.{w, v, u} cof fib Z f) ↔
    ∀ Z, localObjects (C := C) cof fib S Z → mappingTest (C := C) cof fib Z f
  simp only [ho, smallMappingTest_eq.{w, v, u} cof fib hcofW hfibW hcofV hfibV hcofB hfibB]

end SerrePositivity.Bousfield
