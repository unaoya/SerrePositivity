module

public import SerrePositivity.HomotopicalAlgebra.Localization.LeftProperTransfinite
public import SerrePositivity.HomotopicalAlgebra.Localization.LocalFibrantApproximation
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.ClosedObjectwise

/-! # Local equivalence of the actual small boundary generators

Apply Reedy degree induction to the original local-equivalence class,
using its proved closed-class properties. This does not assume a localized
model structure or accessibility of W_S.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy

namespace SerrePositivity.Bousfield
variable {C : Type u} [Category.{v} C] [ModelCategory C] [IsLocallyPresentable.{w} C]
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
  (I J : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]
  [ModelCategory SSet.{w}]
  (IS JS : MorphismProperty SSet.{w}) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} IS JS]
  (hcof : cofibrations SSet.{w} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{w} = SSet.modelCategoryQuillen.J.{w}.rlp)
  (hw : weakEquivalences SSet.{w} = SimplicialHomotopy.weakEquivalences)
  [ModelCategory SSet.{v}] [ModelCategory SSet.{max v w}]
  (hcofV : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfibV : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (hcofB : cofibrations SSet.{max v w} = MorphismProperty.monomorphisms _)
  (hfibB : fibrations SSet.{max v w} = SSet.modelCategoryQuillen.J.{max v w}.rlp)
  [(weakEquivalences C).IsStableUnderCobaseChangeAgainst (cofibrations C)]

local instance : HasColimitsOfSize.{w, w} C := Smith.locallyPresentable_hasColimits (C := C)



include I J IS JS hcof hfib hw hcofV hfibV hcofB hfibB in
lemma arrowFrame_relativeLatching_cof_local (S : MorphismProperty C) (f : Arrow C)
    (hf : localEquivalences.{v, u} (C := C) cof fib S f.hom) (n : SimplexCategory) :
    (cofibrations C ⊓ localEquivalences.{v, u} (C := C) cof fib S)
      (relativeLatchingMap simplex n ((ArrowFrames.inclusion cof).app f)) := by
  let P := cofibrations C ⊓ localEquivalences.{v, u} (C := C) cof fib S
  have hc := localEquivalences_leftProperClosure cof fib I J IS JS hcof hfib hw
    hcofV hfibV hcofB hfibB S
  have := hc.1
  have := hc.2
  have : P.IsStableUnderCoproducts.{w} := MorphismClosure.stableUnderCoproducts P
  have : ∀ n : SimplexCategory, Small.{w} (LatchingIndex simplex n) := fun _ => inferInstance
  have ht (m : SimplexCategory) : localEquivalences.{v, u} (C := C) cof fib S
      (((ArrowFrames.inclusion cof).app f).app m) := by
    intro Y hY
    exact (mappingTest_arrow_iff cof fib hcofV Y (ArrowFrames.degreeArrowComparison cof f m)
      (ArrowFrames.sourceAugmentation_weakEquivalence cof f m)
      (ArrowFrames.targetAugmentation_weakEquivalence cof f m)).mpr (hf Y hY)
  exact ((reedyLeft_inf_iff simplex ((ArrowFrames.inclusion cof).app f)
    (cofibrations C) (localEquivalences.{v, u} (C := C) cof fib S)).mpr
      ⟨ArrowFrames.inclusion_reedyCofibration cof f, ht⟩) n

include I J IS JS hcof hfib hw hcofV hfibV hcofB hfibB in
lemma localBoundaryGenerators_le_cof_local (S : MorphismProperty C) :
    LocalBoundaryGenerators.generators cof S ≤
      cofibrations C ⊓ localEquivalences.{v, u} (C := C) cof fib S := by
  rintro A B g ⟨i⟩
  exact arrowFrame_relativeLatching_cof_local cof fib I J IS JS hcof hfib hw
    hcofV hfibV hcofB hfibB S i.1.val
    (generators_le_localEquivalences cof fib S _ i.1.property) (SimplexCategory.mk i.2)

include I J IS JS hcof hfib hw hcofV hfibV hcofB hfibB in
lemma localFibrantGenerators_le_cof_local (S : MorphismProperty C) :
    LocalFibrantApproximation.generators J cof S ≤
      cofibrations C ⊓ localEquivalences.{v, u} (C := C) cof fib S := by
  apply sup_le
  · intro A B f hf
    have ht : trivialCofibrations C f :=
      (J.le_llp_rlp.trans (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.trivialCofibrations_eq_generated I J).symm.le) f hf
    exact ⟨ht.1, weakEquivalences_le_localEquivalences cof fib hcofV S _ ht.2⟩
  · exact localBoundaryGenerators_le_cof_local cof fib I J IS JS hcof hfib hw
      hcofV hfibV hcofB hfibB S

include I J IS JS hcof hfib hw hcofV hfibV hcofB hfibB in
lemma localFibrant_generated_left_le_cof_local (S : MorphismProperty C) [S.IsSmall.{w}] :
    (LocalFibrantApproximation.generators J cof S).rlp.llp ≤
      cofibrations C ⊓ localEquivalences.{v, u} (C := C) cof fib S := by
  let P := cofibrations C ⊓ localEquivalences.{v, u} (C := C) cof fib S
  have hc := localEquivalences_leftProperClosure cof fib I J IS JS hcof hfib hw
    hcofV hfibV hcofB hfibB S
  have := hc.1
  have := hc.2
  have : P.IsStableUnderCoproducts.{w} := MorphismClosure.stableUnderCoproducts P
  have := LocalFibrantApproximation.generators_isSmall I J cof S
  have := Smith.hasSmallObjectArgument (LocalFibrantApproximation.generators J cof S)
  exact Smith.generatedLeft_le_of_closed _ P
    (localFibrantGenerators_le_cof_local cof fib I J IS JS hcof hfib hw
      hcofV hfibV hcofB hfibB S)

include I J IS JS hcof hfib hw hcofV hfibV hcofB hfibB in
lemma localFibrant_approximation_unit_localEquivalence (S : MorphismProperty C) [S.IsSmall.{w}]
    (d : MorphismProperty.FunctorialFactorizationData
      (LocalFibrantApproximation.generators J cof S).rlp.llp
      (LocalFibrantApproximation.generators J cof S).rlp) (X : C) :
    localEquivalences.{v, u} (C := C) cof fib S
      ((Smith.AccessibleFactorization.terminalComparison d).app X) :=
  (localFibrant_generated_left_le_cof_local cof fib I J IS JS hcof hfib hw
    hcofV hfibV hcofB hfibB S _ (d.hi (Arrow.mk (terminal.from X)))).2

end SerrePositivity.Bousfield
