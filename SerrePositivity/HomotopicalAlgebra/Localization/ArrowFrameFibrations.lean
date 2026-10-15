module

public import SerrePositivity.HomotopicalAlgebra.Localization.ArrowFrameTests
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.RelativeSubcomplexTensor

/-! # Fibrations for the actual locality tests

No cofibrancy assumption is imposed on the ends of the original arrow.
The replacement is the natural Reedy cofibration already constructed in ArrowFrames.
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.HomotopyFunctionComplex

namespace SerrePositivity.Bousfield.ArrowFrames
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))

lemma testMap_hornRLP (f : Arrow C) (Y : C) [IsFibrant Y] :
    SSet.modelCategoryQuillen.J.{v}.rlp (testMap cof f Y) :=
  cosimplicialHomMap_hornRLP _ (source_reedyCofibrant cof f)
    (inclusion_reedyCofibration cof f) (target_reedyCofibrant cof f)
    (source_homotopicallyConstant cof f) (target_homotopicallyConstant cof f) Y

lemma testMap_fibration [ModelCategory SSet.{v}]
    (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
    (f : Arrow C) (Y : C) [IsFibrant Y] : fibrations SSet.{v} (testMap cof f Y) :=
  hfib ▸ testMap_hornRLP cof f Y

lemma testMap_trivialFibration_of_local [ModelCategory SSet.{v}]
    (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))
    (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
    (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
    (S : MorphismProperty C) (Y : C) [IsFibrant Y]
    (hY : localObjects cof fib S Y) (f : Arrow C) (hf : S f.hom) :
    trivialFibrations SSet.{v} (testMap cof f Y) :=
  ⟨testMap_fibration cof hfib f Y,
    (localObjects_iff_of_fibrant cof fib hcof S Y).mp hY f hf⟩

end SerrePositivity.Bousfield.ArrowFrames
