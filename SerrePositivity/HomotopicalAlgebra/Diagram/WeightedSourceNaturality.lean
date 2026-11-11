module

public import SerrePositivity.HomotopicalAlgebra.Diagram.SmallHomWeightFunctoriality
public import SerrePositivity.HomotopicalAlgebra.Diagram.WeightedHomotopyColimitFrame

/-! # Naturality of the actual weighted hocolim source comparison -/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra

namespace SerrePositivity.DiagramModel.WeightedSourceComparison
variable (K : Type w) [SmallCategory K] {C : Type u} [Category.{v} C]
  [ModelCategory C] [IsLocallyPresentable.{w} C]
  (I J : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]

local instance : HasColimitsOfSize.{w, w} C := Smith.locallyPresentable_hasColimits (C := C)

abbrev realizationFamily : (K ⥤ C) ⥤ (Kᵒᵖ ⥤ SSet.{w}) ⥤ C :=
  EvaluatedFrame.family K I J ⋙ SmallHomFrameWeights.family K

@[reassoc]
lemma tail_naturality {D E : K ⥤ C} (f : D ⟶ E) :
    ((realizationFamily K I J).map f).app (ConstantWeightRealization.unitWeight K) ≫
        tail K I J E = tail K I J D ≫ (HomotopyColimit.functor K I J).map f := by
  let a := (EvaluatedFrame.family K I J).map f
  have hn := SmallHomConstantWeight.unitIso_frame_naturality K a
  have hd : SmallHomConstantWeight.degreeMap K a (SimplexCategory.mk 0) =
      (DegreeZeroHomotopyColimit.family K I J).map f := rfl
  have hg : colim.map ((DegreeZeroHomotopyColimit.family K I J).map f) ≫
      (DegreeZeroHomotopyColimit.comparison K I J).app E =
    (DegreeZeroHomotopyColimit.comparison K I J).app D ≫
      (HomotopyColimit.functor K I J).map f :=
        (DegreeZeroHomotopyColimit.comparison K I J).naturality f
  change (SmallHomFrameWeights.map K a).app _ ≫
    ((SmallHomConstantWeight.unitIso K (frames K I J E)).hom ≫ _) =
      ((SmallHomConstantWeight.unitIso K (frames K I J D)).hom ≫ _) ≫ _
  rw [← Category.assoc, hn, hd, Category.assoc,
    hg, ← Category.assoc]

abbrev weightedFamily (W : Kᵒᵖ ⥤ SSet.{w}) : (K ⥤ C) ⥤ SSet.{w} ⥤ C :=
  realizationFamily K I J ⋙
    (Functor.whiskeringLeft SSet.{w} (Kᵒᵖ ⥤ SSet.{w}) C).obj (WeightedCones.tensorDiagram Kᵒᵖ W)

@[reassoc]
lemma comparison_naturality {D E : K ⥤ C} (f : D ⟶ E) {W : Kᵒᵖ ⥤ SSet.{w}}
    (q : W ⟶ ConstantWeightRealization.unitWeight K) :
    ((weightedFamily K I J W).map f).app (𝟙_ SSet.{w}) ≫ comparison K I J E q =
      comparison K I J D q ≫ (HomotopyColimit.functor K I J).map f := by
  let a := (realizationFamily K I J).map f
  have h₁ := a.naturality (unitTensorIso K W).hom
  have h₂ := a.naturality q
  have h₃ := tail_naturality K I J f
  have sq₁ : CommSq _ (a.app ((WeightedCones.tensorDiagram Kᵒᵖ W).obj (𝟙_ SSet.{w})))
      (a.app W) _ := ⟨h₁⟩
  have sq₂ : CommSq _ (a.app W) (a.app (ConstantWeightRealization.unitWeight K)) _ := ⟨h₂⟩
  have sq₃ : CommSq (tail K I J D) (a.app (ConstantWeightRealization.unitWeight K))
      ((HomotopyColimit.functor K I J).map f) (tail K I J E) := ⟨h₃.symm⟩
  exact (sq₁.horiz_comp (sq₂.horiz_comp sq₃)).w.symm

/-- A natural transformation of actual diagram-to-source functors. -/
def comparisonFamily {W : Kᵒᵖ ⥤ SSet.{w}} (q : W ⟶ ConstantWeightRealization.unitWeight K) :
    weightedFamily K I J W ⋙ (evaluation SSet.{w} C).obj (𝟙_ SSet.{w}) ⟶
      HomotopyColimit.functor K I J where
  app D := comparison K I J D q
  naturality _ _ f := comparison_naturality K I J f q

end SerrePositivity.DiagramModel.WeightedSourceComparison

namespace SerrePositivity.DiagramModel.WeightedHomotopyColimitFrame
variable (K : Type w) [SmallCategory K] {C : Type u} [Category.{v} C]
  [ModelCategory C] [IsLocallyPresentable.{w} C]
  (I J : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]
  [ModelCategory SSet.{w}]
  (IS JS : MorphismProperty SSet.{w}) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} IS JS]

abbrev leftFamily : (K ⥤ C) ⥤ SSet.{w} ⥤ C :=
  WeightedSourceComparison.weightedFamily K I J (HomotopyCones.weight Kᵒᵖ IS JS)

abbrev frameFamily : (K ⥤ C) ⥤ SimplexCategory ⥤ C :=
  leftFamily K I J IS JS ⋙ (Functor.whiskeringLeft SimplexCategory SSet.{w} C).obj SSet.stdSimplex

/-- The original degreewise augmentation is natural in the source diagram as well. -/
def augmentationFamily : frameFamily K I J IS JS ⟶
    HomotopyColimit.functor K I J ⋙ Functor.const SimplexCategory where
  app D := augmentation K I J IS JS D
  naturality D E f := by
    apply NatTrans.ext
    funext n
    let a := (leftFamily K I J IS JS).map f
    have hn := a.naturality (HomotopyFunctionComplex.QuillenStandardFrame.augmentation.app n)
    have hc := WeightedSourceComparison.comparison_naturality K I J f
      (HomotopyCones.weightComparison Kᵒᵖ IS JS)
    have sq₁ : CommSq _ (a.app (SSet.stdSimplex.obj n))
        (a.app (𝟙_ SSet.{w})) _ := ⟨hn⟩
    have sq₂ : CommSq (WeightedSourceComparison.comparison K I J D
        (HomotopyCones.weightComparison Kᵒᵖ IS JS)) (a.app (𝟙_ SSet.{w}))
      ((HomotopyColimit.functor K I J).map f)
      (WeightedSourceComparison.comparison K I J E
        (HomotopyCones.weightComparison Kᵒᵖ IS JS)) := ⟨hc.symm⟩
    exact (sq₁.horiz_comp sq₂).w.symm

end SerrePositivity.DiagramModel.WeightedHomotopyColimitFrame
