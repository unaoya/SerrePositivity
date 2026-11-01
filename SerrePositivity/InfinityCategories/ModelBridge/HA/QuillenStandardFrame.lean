module

public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FramePreservation
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.QuillenStandardFrame
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.StandardCosimplicial
public import SerrePositivity.HomotopicalAlgebra.Simplicial.StandardSimplexWeakEquivalence

/-!
分割で生成：docstring を書き直すこと
 # Standard cosimplicial frames under a left Quillen left adjoint

The source and target Hom universes are independent. The augmentation is
the actual collapse to the zero-simplex followed by the terminal-unit iso.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.Reedy

namespace SerrePositivity.HomotopyFunctionComplex.QuillenStandardFrame

variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{w}]
  (L : SSet.{w} ⥤ C) [L.IsLeftAdjoint] [Quillen.IsLeftQuillen L]
  (hcof : cofibrations SSet.{w} = MorphismProperty.monomorphisms _)
  (hw : weakEquivalences SSet.{w} = SimplicialHomotopy.weakEquivalences)

include hcof in
lemma reedyCofibrant : reedyLeft simplex (cofibrations C)
    (initial.to (SSet.stdSimplex ⋙ L)) := by
  have hs := StandardCosimplicial.reedy_cofibrant (𝟭 SSet.{w}) hcof
  exact leftQuillen_frame_reedyCofibrant L SSet.stdSimplex hs

omit [L.IsLeftAdjoint] in
include hcof hw in
lemma augmentation_weakEquivalence (n : SimplexCategory) :
    weakEquivalences C (L.map (augmentation.app n)) := by
  have : IsCofibrant (SSet.stdSimplex.{w}.obj n) := by
    constructor
    rw [hcof]
    change Mono _
    infer_instance
  have : IsCofibrant (𝟙_ SSet.{w}) := by
    constructor
    rw [hcof]
    change Mono _
    infer_instance
  have ha : weakEquivalences SSet.{w} (augmentation.app n) :=
    (weakEquivalences SSet.{w}).comp_mem _ _
      (hw.symm ▸ SimplicialHomotopy.stdSimplex_map_weakEquivalence (collapse n))
      ((weakEquivalences SSet.{w}).of_isIso zeroUnitIso.hom)
  have : IsCofibrant (((Functor.const SimplexCategory).obj (𝟙_ SSet.{w})).obj n) :=
    inferInstanceAs (IsCofibrant (𝟙_ SSet.{w}))
  have : WeakEquivalence (augmentation.app n) := ⟨ha⟩
  exact (weakEquivalence_iff _).mp (Quillen.map_weakEquivalence_of_cofibrant L (augmentation.app n))

end SerrePositivity.HomotopyFunctionComplex.QuillenStandardFrame
