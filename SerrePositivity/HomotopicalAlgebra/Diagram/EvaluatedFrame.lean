module

public import SerrePositivity.HomotopicalAlgebra.Diagram.ColimitFrame
public import SerrePositivity.HomotopicalAlgebra.Diagram.ProjectiveCofibrations
public import Mathlib.CategoryTheory.Functor.Currying

/-! # Evaluating a projective cosimplicial frame at every diagram point

Evaluation preserves the latching colimits and projective cofibrations.
Thus all pointwise source objects are actual cosimplicial frames, naturally
in the diagram and its index. Their augmentation to the original diagram
is a pointwise weak equivalence, even when that diagram is not cofibrant.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy SerrePositivity.HomotopyFunctionComplex

namespace SerrePositivity.DiagramModel.EvaluatedFrame
variable (K : Type w) [SmallCategory K] {C : Type u} [Category.{v} C]
  [ModelCategory C] [IsLocallyPresentable.{w} C]
  (I J : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]

abbrev family : (K ⥤ C) ⥤ K ⥤ (SimplexCategory ⥤ C) :=
  ColimitFrame.diagramResolution K I J ⋙ flipFunctor SimplexCategory K C

abbrev frame : ((K ⥤ C) × K) ⥤ (SimplexCategory ⥤ C) := Functor.uncurry.obj (family K I J)

abbrev originalEvaluation : ((K ⥤ C) × K) ⥤ C := Functor.uncurry.obj (𝟭 (K ⥤ C))

abbrev replacementEvaluation : ((K ⥤ C) × K) ⥤ C :=
  Functor.uncurry.obj (HomotopyColimit.replacement K I J)

def diagramAugmentation : ColimitFrame.diagramResolution K I J ⟶
    HomotopyColimit.replacement K I J ⋙ Functor.const SimplexCategory := by
  let := Projective.modelCategory K I J
  exact Functor.whiskerLeft (HomotopyColimit.replacement K I J)
    (ColimitFrame.resolutionFamily K I J).augmentation

def frameAugmentation : frame K I J ⟶
    replacementEvaluation K I J ⋙ Functor.const SimplexCategory :=
  Functor.uncurry.map (Functor.whiskerRight (diagramAugmentation K I J)
    (flipFunctor SimplexCategory K C))

def augmentation : frame K I J ⟶ originalEvaluation K (C := C) ⋙
    Functor.const SimplexCategory :=
  frameAugmentation K I J ≫ Functor.whiskerRight
    (Functor.uncurry.map (HomotopyColimit.replacementComparison K I J))
    (Functor.const SimplexCategory)

lemma reedyCofibrant (x : (K ⥤ C) × K) :
    reedyLeft simplex (cofibrations C) (initial.to ((frame K I J).obj x)) := by
  let := Projective.modelCategory K I J
  let A := (ColimitFrame.diagramResolution K I J).obj x.1
  let E := (CategoryTheory.evaluation K C).obj x.2
  have hA : reedyLeft simplex (cofibrations (K ⥤ C)) (initial.to A) :=
    (ColimitFrame.resolutionFamily K I J).cofibrant
      ((HomotopyColimit.replacement K I J).obj x.1)
  exact reedyCofibrant_of_preservesLatching simplex E A (fun _ => inferInstance)
    (fun _ _ f hf => Projective.cofibrations_le_objectwise K I J f hf x.2) hA

lemma frameAugmentation_weakEquivalence (x : (K ⥤ C) × K) (n : SimplexCategory) :
    weakEquivalences C (((frameAugmentation K I J).app x).app n) := by
  let := Projective.modelCategory K I J
  exact ((ColimitFrame.resolutionFamily K I J).atObject
    ((HomotopyColimit.replacement K I J).obj x.1)).augmentation_weakEquivalence n x.2

lemma augmentation_weakEquivalence (x : (K ⥤ C) × K) (n : SimplexCategory) :
    weakEquivalences C (((augmentation K I J).app x).app n) :=
  (weakEquivalences C).comp_mem _ _ (frameAugmentation_weakEquivalence K I J x n)
    (HomotopyColimit.replacementComparison_objectwiseWeakEquivalence K I J x.1 x.2)

lemma homotopicallyConstant (x : (K ⥤ C) × K) {n m : SimplexCategory} (f : n ⟶ m) :
    weakEquivalences C (((frame K I J).obj x).map f) := by
  let := Projective.modelCategory K I J
  exact ((ColimitFrame.resolutionFamily K I J).atObject
    ((HomotopyColimit.replacement K I J).obj x.1)).homotopicallyConstant f x.2

lemma hom_kanComplex (x : (K ⥤ C) × K) (Y : C) [IsFibrant Y] :
    SSet.KanComplex ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom ((frame K I J).obj x)).obj Y) :=
  cosimplicialHom_kanComplex _ (reedyCofibrant K I J x) (homotopicallyConstant K I J x) Y

end SerrePositivity.DiagramModel.EvaluatedFrame
