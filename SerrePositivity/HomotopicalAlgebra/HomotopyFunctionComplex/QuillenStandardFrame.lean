module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FramePreservation
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.StandardCosimplicial
public import SerrePositivity.HomotopicalAlgebra.Simplicial.StandardSimplexWeakEquivalence
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

/-! # Standard cosimplicial frames under a left Quillen left adjoint

The source and target Hom universes are independent. The augmentation is
the actual collapse to the zero-simplex followed by the terminal-unit iso.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.Reedy

namespace SerrePositivity.HomotopyFunctionComplex.QuillenStandardFrame

abbrev zeroUnitIso : SSet.stdSimplex.{w}.obj (SimplexCategory.mk 0) ≅ (𝟙_ SSet.{w}) :=
  SSet.stdSimplex.isTerminalObj₀.uniqueUpToIso CartesianMonoidalCategory.isTerminalTensorUnit

abbrev collapse (n : SimplexCategory) : n ⟶ SimplexCategory.mk 0 :=
  SimplexCategory.const n (SimplexCategory.mk 0) 0

def augmentation : SSet.stdSimplex.{w} ⟶ (Functor.const SimplexCategory).obj (𝟙_ SSet.{w}) where
  app n := SSet.stdSimplex.map (collapse n) ≫ zeroUnitIso.hom
  naturality n m f := by
    have hc : f ≫ collapse m = collapse n := by ext i; rfl
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id,
      ← Category.assoc, ← Functor.map_comp, hc]

/-- The actual cosimplicial Hom of standard simplices is the simplicial set itself. -/
def homIso : cosimplicialHom SSet.stdSimplex.{w} ≅ 𝟭 SSet.{w} :=
  NatIso.ofComponents (fun Y => NatIso.ofComponents (fun n =>
    Equiv.toIso (SSet.yonedaEquiv (X := Y) (n := n.unop))) (by
      intro n m f
      ext a
      exact (SSet.yonedaEquiv_naturality f.unop a).symm)) (by
    intro Y Z f
    ext n a
    exact SSet.yonedaEquiv_comp a f)

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
