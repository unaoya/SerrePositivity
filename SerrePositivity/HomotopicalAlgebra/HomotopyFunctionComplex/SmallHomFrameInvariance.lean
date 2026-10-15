module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.SmallHomComparison
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.SourceInvariance

/-! # Weak frame comparisons under the actual small-Hom bifunctor

The proof works in the transferred small-Hom model directly. It needs a
simplicial value model only in the presentability universe, rather than
models in the original Hom universe and a common larger universe.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy

namespace SerrePositivity.HomotopyFunctionComplex.SmallHomComparison
variable {C : Type u} [Category.{v} C] [ModelCategory C] [IsLocallyPresentable.{w} C]
  [ModelCategory SSet.{w}]
  (hcof : cofibrations SSet.{w} = MorphismProperty.monomorphisms _)

include hcof in
lemma map_frame_weakEquivalence {A B : SimplexCategory ⥤ C} (a : A ⟶ B)
    (hA : reedyLeft simplex (cofibrations C) (initial.to A))
    (hB : reedyLeft simplex (cofibrations C) (initial.to B))
    (ha : ∀ n, weakEquivalences C (a.app n)) (Y : C) [IsFibrant Y] :
    weakEquivalences SSet.{w} ((bifunctor.map a.op).app Y) := by
  let := SmallHomModel.modelCategory.{w} C
  let R := changeHom (C := C)
  have : R.IsRightAdjoint := (SmallHomModel.equivalence.{w} C).toAdjunction.isRightAdjoint
  have : Quillen.IsRightQuillen R := SmallHomModel.fromOriginal_isRightQuillen.{w} C
  have : IsFibrant (R.obj Y) :=
    (isFibrant_iff_of_isTerminal (R.map (terminal.from Y))
      (terminalIsTerminal.isTerminalObj R (⊤_ C))).mpr (Quillen.map_fibration R (terminal.from Y))
  have : Quillen.IsLeftQuillen R := SmallHomModel.fromOriginal_isLeftQuillen.{w} C
  have hw (n : SimplexCategory) : weakEquivalences (ShrinkHoms C) (R.map (a.app n)) := by
    have := cosimplicialFrame_isCofibrant_obj A hA n
    have := cosimplicialFrame_isCofibrant_obj B hB n
    have : WeakEquivalence (a.app n) := ⟨ha n⟩
    exact (weakEquivalence_iff _).mp (Quillen.map_weakEquivalence_of_cofibrant R (a.app n))
  exact cosimplicialHomMap_weakEquivalence hcof (Functor.whiskerRight a R)
    (SmallHomRealization.frame_reedyCofibrant A hA)
    (SmallHomRealization.frame_reedyCofibrant B hB) hw (R.obj Y)

end SerrePositivity.HomotopyFunctionComplex.SmallHomComparison
