module
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.QuillenStandardFrame

public import SerrePositivity.HomotopicalAlgebra.Diagram.WeightedSourceWeakEquivalence
public import SerrePositivity.HomotopicalAlgebra.Diagram.FrameWeightedLimit
public import SerrePositivity.HomotopicalAlgebra.Simplicial.StandardSimplexCosimplicialHom

/-! # An actual cosimplicial frame over the specified homotopy colimit

The weighted Quillen adjunction applied to standard simplices gives a
Reedy cofibrant object, weakly augmented over the original hocolim. Its
actual Hom identifies with weighted frame Hom after the explicit common
universe lift. Source-diagram naturality is a separate remaining step.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.Reedy SerrePositivity.HomotopyFunctionComplex

namespace SerrePositivity.DiagramModel.WeightedHomotopyColimitFrame
variable (K : Type w) [SmallCategory K] {C : Type u} [Category.{v} C]
  [ModelCategory C] [IsLocallyPresentable.{w} C]
  (I J : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]
  [ModelCategory SSet.{w}]
  (IS JS : MorphismProperty SSet.{w}) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} IS JS]
  (D : K ⥤ C)

abbrev left : SSet.{w} ⥤ C :=
  FrameWeightedLimit.weightedFunctor K IS JS (WeightedSourceComparison.frames K I J D)

abbrev frame : SimplexCategory ⥤ C := SSet.stdSimplex ⋙ left K I J IS JS D

def augmentation : frame K I J IS JS D ⟶
    (Functor.const SimplexCategory).obj ((HomotopyColimit.functor K I J).obj D) := by
  refine Functor.whiskerRight QuillenStandardFrame.augmentation (left K I J IS JS D) ≫ ?_
  exact {
    app := fun _ => WeightedSourceComparison.comparison K I J D
      (HomotopyCones.weightComparison Kᵒᵖ IS JS)
    naturality := by
      intro n m f
      change (left K I J IS JS D).map (𝟙 _) ≫ _ = _ ≫ 𝟙 _
      rw [(left K I J IS JS D).map_id]
      simp }

/-- Both sides are actual simplicial sets, with their original Hom universes explicit. -/
def homIso : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (frame K I J IS JS D) ⋙ SSet.uliftFunctor.{w,v} ≅
    FrameWeightedLimit.weightedHom K IS JS (WeightedSourceComparison.frames K I J D) ⋙
      SSet.uliftFunctor.{v,w} :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.adjunctionHomIso (FrameWeightedLimit.adjunction K IS JS (WeightedSourceComparison.frames K I J D))
    SSet.stdSimplex ≪≫ Functor.isoWhiskerLeft _
      (Functor.isoWhiskerRight QuillenStandardFrame.homIso SSet.uliftFunctor ≪≫
        Functor.leftUnitor _)

variable (hcof : cofibrations SSet.{w} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{w} = SSet.modelCategoryQuillen.J.{w}.rlp)
  (hw : weakEquivalences SSet.{w} = SimplicialHomotopy.weakEquivalences)

include hcof hfib in
lemma reedyCofibrant : reedyLeft simplex (cofibrations C)
    (initial.to (frame K I J IS JS D)) := by
  have := (FrameWeightedLimit.adjunction K IS JS
    (WeightedSourceComparison.frames K I J D)).isLeftAdjoint
  have := FrameWeightedLimit.weighted_isLeftQuillen K IS JS hcof hfib
    (WeightedSourceComparison.frames K I J D)
    (fun k => EvaluatedFrame.reedyCofibrant K I J (D, k))
    (fun k => EvaluatedFrame.homotopicallyConstant K I J (D, k))
  exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.QuillenStandardFrame.reedyCofibrant (left K I J IS JS D) hcof

include hcof hfib hw in
lemma augmentation_weakEquivalence (n : SimplexCategory) :
    weakEquivalences C ((augmentation K I J IS JS D).app n) := by
  have := (FrameWeightedLimit.adjunction K IS JS
    (WeightedSourceComparison.frames K I J D)).isLeftAdjoint
  have := FrameWeightedLimit.weighted_isLeftQuillen K IS JS hcof hfib
    (WeightedSourceComparison.frames K I J D)
    (fun k => EvaluatedFrame.reedyCofibrant K I J (D, k))
    (fun k => EvaluatedFrame.homotopicallyConstant K I J (D, k))
  exact (weakEquivalences C).comp_mem _ _
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.QuillenStandardFrame.augmentation_weakEquivalence (left K I J IS JS D) hcof hw n)
    (WeightedSourceComparison.comparison_weakEquivalence K I J IS JS hcof hfib D)

end SerrePositivity.DiagramModel.WeightedHomotopyColimitFrame
