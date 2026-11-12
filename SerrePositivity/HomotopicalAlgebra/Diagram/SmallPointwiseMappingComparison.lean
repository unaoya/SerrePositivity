module

public import SerrePositivity.HomotopicalAlgebra.Diagram.PointwiseMappingComparison
public import SerrePositivity.HomotopicalAlgebra.Diagram.SmallHomWeightAdjunctionNaturality
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.SmallHomFrameInvariance

/-! # Pointwise chosen RMap comparison in the actual small-Hom universe

The original specified resolutions and fibrant replacements are retained.
The cospan is natural in the diagram, its index and the target, and needs
only the simplicial model in the presentability universe.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy SerrePositivity.HomotopyFunctionComplex

namespace SerrePositivity.DiagramModel.SmallPointwiseMappingComparison
variable (K : Type w) [SmallCategory K] {C : Type u} [Category.{v} C]
  [ModelCategory C] [IsLocallyPresentable.{w} C]
  (I J : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))

abbrev diagrams (A : ((K ⥤ C) × K) ⥤ SimplexCategory ⥤ C) :
    (K ⥤ C)ᵒᵖ ⥤ C ⥤ Kᵒᵖ ⥤ SSet.{w} :=
  Functor.curry.obj ((prodOpEquiv (C := K ⥤ C) (D := K)).inverse ⋙
    A.op ⋙ SmallHomComparison.bifunctor ⋙
      (Functor.whiskeringLeft C C SSet.{w}).obj (fibrantTarget fib)) ⋙
        flipFunctor Kᵒᵖ C SSet.{w}

abbrev diagramsMap {A B : ((K ⥤ C) × K) ⥤ SimplexCategory ⥤ C} (a : A ⟶ B) :
    diagrams K fib B ⟶ diagrams K fib A :=
  Functor.whiskerRight (Functor.curry.map (Functor.whiskerLeft
    (prodOpEquiv (C := K ⥤ C) (D := K)).inverse
    (Functor.whiskerRight (NatTrans.op a)
      (SmallHomComparison.bifunctor ⋙
        (Functor.whiskeringLeft C C SSet.{w}).obj (fibrantTarget fib)))))
    (flipFunctor Kᵒᵖ C SSet.{w})

abbrev resolvedDiagram := diagrams K fib
  (EvaluatedFrame.originalEvaluation K ⋙ (cosimplicialResolutionFamily cof).obj)
abbrev frameDiagram := diagrams K fib (EvaluatedFrame.frame K I J)
abbrev middle := diagrams K fib (PointwiseMappingComparison.commonFrame K I J cof)

abbrev pointwiseRMap : (K ⥤ C)ᵒᵖ ⥤ C ⥤ Kᵒᵖ ⥤ SSet.{w} :=
  Functor.opHom K C ⋙
    (Functor.whiskeringRight Kᵒᵖ Cᵒᵖ (C ⥤ SSet.{w})).obj (SmallHomComparison.chosenHom cof fib) ⋙
      flipFunctor Kᵒᵖ C SSet.{w}

def pointwiseRMapIso : resolvedDiagram K cof fib ≅ pointwiseRMap K cof fib :=
  NatIso.ofComponents (fun D => NatIso.ofComponents (fun Y =>
    NatIso.ofComponents (fun _ => Iso.refl _) (by
      intro k l f
      ext n h
      simp [resolvedDiagram, diagrams, pointwiseRMap, EvaluatedFrame.originalEvaluation,
        SmallHomComparison.chosenHom, SmallHomComparison.hom, SmallHomComparison.bifunctor])) (by
      intro Y Z f
      ext k n h
      rfl)) (by
    intro D E f
    ext Y k n h
    simp [resolvedDiagram, diagrams, pointwiseRMap, EvaluatedFrame.originalEvaluation,
      SmallHomComparison.chosenHom, SmallHomComparison.hom, SmallHomComparison.bifunctor])

abbrev evaluatedHom : (K ⥤ C)ᵒᵖ ⥤ C ⥤ Kᵒᵖ ⥤ SSet.{w} :=
  (EvaluatedFrame.family K I J).op ⋙ SmallHomFrameWeights.homFamily K ⋙
    (Functor.whiskeringLeft C C (Kᵒᵖ ⥤ SSet.{w})).obj (fibrantTarget fib)

def frameDiagramIso : frameDiagram K I J fib ≅ evaluatedHom K I J fib :=
  NatIso.ofComponents (fun D => NatIso.ofComponents (fun Y =>
    NatIso.ofComponents (fun _ => Iso.refl _) (by
      intro k l f
      ext n h
      simp [frameDiagram, diagrams, evaluatedHom, EvaluatedFrame.frame, EvaluatedFrame.family,
        SmallHomFrameWeights.homFamily, SmallHomFrameWeights.sourceFamily,
        FrameWeightRealization.homFamily, SmallHomComparison.bifunctor])) (by
      intro Y Z f
      ext k n h
      rfl)) (by
    intro D E f
    ext Y k n h
    simp [frameDiagram, diagrams, evaluatedHom, EvaluatedFrame.frame, EvaluatedFrame.family,
      SmallHomFrameWeights.homFamily, SmallHomFrameWeights.sourceFamily,
      FrameWeightRealization.homFamily, SmallHomComparison.bifunctor])

abbrev resolvedLeft : resolvedDiagram K cof fib ⟶ middle K I J cof fib :=
  diagramsMap K fib (FrameOverFunctor.left cof (cosimplicialResolutionFamily cof)
    (EvaluatedFrame.originalEvaluation K) (EvaluatedFrame.frame K I J)
    (EvaluatedFrame.augmentation K I J))

abbrev frameRight : frameDiagram K I J fib ⟶ middle K I J cof fib :=
  diagramsMap K fib (FrameOverFunctor.right cof (cosimplicialResolutionFamily cof)
    (EvaluatedFrame.originalEvaluation K) (EvaluatedFrame.frame K I J)
    (EvaluatedFrame.augmentation K I J))

abbrev left : pointwiseRMap K cof fib ⟶ middle K I J cof fib :=
  (pointwiseRMapIso K cof fib).inv ≫ resolvedLeft K I J cof fib
abbrev right : evaluatedHom K I J fib ⟶ middle K I J cof fib :=
  (frameDiagramIso K I J fib).inv ≫ frameRight K I J cof fib

variable [ModelCategory SSet.{w}]
  (hcof : cofibrations SSet.{w} = MorphismProperty.monomorphisms _)

include hcof in
lemma resolvedLeft_weakEquivalence (D : (K ⥤ C)ᵒᵖ) (Y : C) (k : Kᵒᵖ) :
    weakEquivalences SSet.{w} ((((resolvedLeft K I J cof fib).app D).app Y).app k) := by
  have := fibrantTarget_isFibrant fib Y
  exact SmallHomComparison.map_frame_weakEquivalence hcof
    ((FrameOverFunctor.left cof (cosimplicialResolutionFamily cof)
      (EvaluatedFrame.originalEvaluation K) (EvaluatedFrame.frame K I J)
      (EvaluatedFrame.augmentation K I J)).app (D.unop, k.unop))
    (FrameOverFunctor.commonObj_cofibrant cof (cosimplicialResolutionFamily cof)
      (EvaluatedFrame.originalEvaluation K) (EvaluatedFrame.frame K I J)
      (EvaluatedFrame.augmentation K I J) (D.unop, k.unop))
    ((cosimplicialResolutionFamily cof).cofibrant (D.unop.obj k.unop))
    (FrameOverFunctor.left_weakEquivalence cof (cosimplicialResolutionFamily cof)
      (EvaluatedFrame.originalEvaluation K) (EvaluatedFrame.frame K I J)
      (EvaluatedFrame.augmentation K I J) (EvaluatedFrame.augmentation_weakEquivalence K I J)
      (D.unop, k.unop)) ((fibrantTarget fib).obj Y)

include hcof in
lemma frameRight_weakEquivalence (D : (K ⥤ C)ᵒᵖ) (Y : C) (k : Kᵒᵖ) :
    weakEquivalences SSet.{w} ((((frameRight K I J cof fib).app D).app Y).app k) := by
  have := fibrantTarget_isFibrant fib Y
  exact SmallHomComparison.map_frame_weakEquivalence hcof
    ((FrameOverFunctor.right cof (cosimplicialResolutionFamily cof)
      (EvaluatedFrame.originalEvaluation K) (EvaluatedFrame.frame K I J)
      (EvaluatedFrame.augmentation K I J)).app (D.unop, k.unop))
    (FrameOverFunctor.commonObj_cofibrant cof (cosimplicialResolutionFamily cof)
      (EvaluatedFrame.originalEvaluation K) (EvaluatedFrame.frame K I J)
      (EvaluatedFrame.augmentation K I J) (D.unop, k.unop))
    (EvaluatedFrame.reedyCofibrant K I J (D.unop, k.unop))
    (FrameOverFunctor.right_weakEquivalence cof (cosimplicialResolutionFamily cof)
      (EvaluatedFrame.originalEvaluation K) (EvaluatedFrame.frame K I J)
      (EvaluatedFrame.augmentation K I J) (D.unop, k.unop)) ((fibrantTarget fib).obj Y)

include hcof in
lemma left_weakEquivalence (D : (K ⥤ C)ᵒᵖ) (Y : C) (k : Kᵒᵖ) :
    weakEquivalences SSet.{w} ((((left K I J cof fib).app D).app Y).app k) :=
  (weakEquivalences SSet.{w}).comp_mem _ _ ((weakEquivalences SSet.{w}).of_isIso _)
    (resolvedLeft_weakEquivalence K I J cof fib hcof D Y k)

include hcof in
lemma right_weakEquivalence (D : (K ⥤ C)ᵒᵖ) (Y : C) (k : Kᵒᵖ) :
    weakEquivalences SSet.{w} ((((right K I J cof fib).app D).app Y).app k) :=
  (weakEquivalences SSet.{w}).comp_mem _ _ ((weakEquivalences SSet.{w}).of_isIso _)
    (frameRight_weakEquivalence K I J cof fib hcof D Y k)

end SerrePositivity.DiagramModel.SmallPointwiseMappingComparison
