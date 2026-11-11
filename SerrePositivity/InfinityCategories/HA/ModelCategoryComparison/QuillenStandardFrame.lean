module
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FramePreservation
public import SerrePositivity.HomotopicalAlgebra.Simplicial.FiniteTensorAdjunction
public import SerrePositivity.HomotopicalAlgebra.Simplicial.StandardSimplexCosimplicialHom
public import SerrePositivity.HomotopicalAlgebra.Simplicial.StandardSimplexWeakEquivalence
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.StandardCosimplicial
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.R72.FiniteTensorAdjunction


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

namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.QuillenStandardFrame

variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{w}]
  (L : SSet.{w} ⥤ C) [L.IsLeftAdjoint] [Quillen.IsLeftQuillen L]
  (hcof : cofibrations SSet.{w} = MorphismProperty.monomorphisms _)
  (hw : weakEquivalences SSet.{w} = SimplicialHomotopy.weakEquivalences)

include hcof in
lemma reedyCofibrant : reedyLeft simplex (cofibrations C)
    (initial.to (SSet.stdSimplex ⋙ L)) := by
  have hs := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.reedy_cofibrant (𝟭 SSet.{w}) hcof
  exact _root_.SerrePositivity.HomotopyFunctionComplex.leftQuillen_frame_reedyCofibrant L SSet.stdSimplex hs

omit [L.IsLeftAdjoint] in
include hcof hw in
lemma augmentation_weakEquivalence (n : SimplexCategory) :
    weakEquivalences C (L.map (_root_.SerrePositivity.HomotopyFunctionComplex.QuillenStandardFrame.augmentation.app n)) := by
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
  have ha : weakEquivalences SSet.{w} (_root_.SerrePositivity.HomotopyFunctionComplex.QuillenStandardFrame.augmentation.app n) :=
    (weakEquivalences SSet.{w}).comp_mem _ _
      (hw.symm ▸ SimplicialHomotopy.stdSimplex_map_weakEquivalence (_root_.SerrePositivity.HomotopyFunctionComplex.QuillenStandardFrame.collapse n))
      ((weakEquivalences SSet.{w}).of_isIso _root_.SerrePositivity.HomotopyFunctionComplex.QuillenStandardFrame.zeroUnitIso.hom)
  have : IsCofibrant (((Functor.const SimplexCategory).obj (𝟙_ SSet.{w})).obj n) :=
    inferInstanceAs (IsCofibrant (𝟙_ SSet.{w}))
  have : WeakEquivalence (_root_.SerrePositivity.HomotopyFunctionComplex.QuillenStandardFrame.augmentation.app n) := ⟨ha⟩
  exact (weakEquivalence_iff _).mp (Quillen.map_weakEquivalence_of_cofibrant L (_root_.SerrePositivity.HomotopyFunctionComplex.QuillenStandardFrame.augmentation.app n))

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.QuillenStandardFrame
