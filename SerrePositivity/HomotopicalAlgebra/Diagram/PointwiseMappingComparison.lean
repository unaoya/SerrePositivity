module

public import SerrePositivity.HomotopicalAlgebra.Diagram.EvaluatedFrame
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameOverFunctor

/-! # Natural comparison of the pointwise RMap diagrams

The source parameter combines a diagram and its index. The common frame
comparison is therefore natural in the diagram, the index and the target,
not a family of unrelated pointwise comparisons.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy SerrePositivity.HomotopyFunctionComplex

namespace SerrePositivity.DiagramModel.PointwiseMappingComparison
variable (K : Type w) [SmallCategory K] {C : Type u} [Category.{v} C]
  [ModelCategory C] [IsLocallyPresentable.{w} C]
  (I J : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))

abbrev commonFrame := FrameOverFunctor.commonObj cof (cosimplicialResolutionFamily cof)
  (EvaluatedFrame.originalEvaluation K (C := C))
  (EvaluatedFrame.frame K I J) (EvaluatedFrame.augmentation K I J)

/-- Repackage the actual Hom into K-opposite diagrams, retaining both parameters. -/
abbrev diagrams (A : ((K ⥤ C) × K) ⥤ (SimplexCategory ⥤ C)) :
    (K ⥤ C)ᵒᵖ ⥤ C ⥤ Kᵒᵖ ⥤ SSet.{v} :=
  Functor.curry.obj ((CategoryTheory.prodOpEquiv (C := K ⥤ C) (D := K)).inverse ⋙
    FrameOverFunctor.hom A ⋙ (Functor.whiskeringLeft C C SSet.{v}).obj (fibrantTarget fib)) ⋙
      flipFunctor Kᵒᵖ C SSet.{v}

/-- Source changes remain natural transformations of the entire diagram-valued bifunctor. -/
abbrev diagramsMap {A B : ((K ⥤ C) × K) ⥤ (SimplexCategory ⥤ C)} (a : A ⟶ B) :
    diagrams K fib B ⟶ diagrams K fib A :=
  Functor.whiskerRight (Functor.curry.map (Functor.whiskerLeft
    (CategoryTheory.prodOpEquiv (C := K ⥤ C) (D := K)).inverse
    (Functor.whiskerRight (NatTrans.op a)
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomBifunctor ⋙ (Functor.whiskeringLeft C C SSet.{v}).obj (fibrantTarget fib)))))
    (flipFunctor Kᵒᵖ C SSet.{v})

abbrev resolvedDiagram : (K ⥤ C)ᵒᵖ ⥤ C ⥤ Kᵒᵖ ⥤ SSet.{v} :=
  diagrams K fib (EvaluatedFrame.originalEvaluation K ⋙ (cosimplicialResolutionFamily cof).obj)

abbrev frameDiagram : (K ⥤ C)ᵒᵖ ⥤ C ⥤ Kᵒᵖ ⥤ SSet.{v} :=
  diagrams K fib (EvaluatedFrame.frame K I J)

abbrev middle : (K ⥤ C)ᵒᵖ ⥤ C ⥤ Kᵒᵖ ⥤ SSet.{v} :=
  diagrams K fib (commonFrame K I J cof)

abbrev left : resolvedDiagram K cof fib ⟶ middle K I J cof fib :=
  diagramsMap K fib (FrameOverFunctor.left cof (cosimplicialResolutionFamily cof)
    (EvaluatedFrame.originalEvaluation K) (EvaluatedFrame.frame K I J)
    (EvaluatedFrame.augmentation K I J))

abbrev right : frameDiagram K I J fib ⟶ middle K I J cof fib :=
  diagramsMap K fib (FrameOverFunctor.right cof (cosimplicialResolutionFamily cof)
    (EvaluatedFrame.originalEvaluation K) (EvaluatedFrame.frame K I J)
    (EvaluatedFrame.augmentation K I J))

abbrev pointwiseRMap : (K ⥤ C)ᵒᵖ ⥤ C ⥤ Kᵒᵖ ⥤ SSet.{v} :=
  Functor.opHom K C ⋙
    (Functor.whiskeringRight Kᵒᵖ Cᵒᵖ (C ⥤ SSet.{v})).obj (chosenResolutionHom cof fib) ⋙
      flipFunctor Kᵒᵖ C SSet.{v}

/-- The repackaged source really is the strict diagram k ↦ RMap(D(k),Y). -/
def pointwiseRMapIso : resolvedDiagram K cof fib ≅ pointwiseRMap K cof fib :=
  NatIso.ofComponents (fun F => NatIso.ofComponents (fun Y =>
    NatIso.ofComponents (fun _ => Iso.refl _) (by
      intro k l f
      ext n h
      simp [resolvedDiagram, diagrams, pointwiseRMap, FrameOverFunctor.hom,
        EvaluatedFrame.originalEvaluation, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.resolutionHom, chosenResolutionHom,
        _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomBifunctor, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap])) (by
      intro Y Z g
      ext k n h
      rfl)) (by
    intro F G f
    ext Y k n h
    simp [resolvedDiagram, diagrams, pointwiseRMap, FrameOverFunctor.hom,
      EvaluatedFrame.originalEvaluation, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.resolutionHom, chosenResolutionHom,
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomBifunctor, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap])

abbrev pointwiseLeft : pointwiseRMap K cof fib ⟶ middle K I J cof fib :=
  (pointwiseRMapIso K cof fib).inv ≫ left K I J cof fib

omit [IsLocallyPresentable.{w} C] in
@[simp]
lemma resolvedDiagram_obj (F : (K ⥤ C)ᵒᵖ) (Y : C) (k : Kᵒᵖ) :
    (((resolvedDiagram K cof fib).obj F).obj Y).obj k =
      ((chosenResolutionHom cof fib).obj (Opposite.op (F.unop.obj k.unop))).obj Y := rfl

lemma middle_kanComplex (F : (K ⥤ C)ᵒᵖ) (Y : C) (k : Kᵒᵖ) :
    SSet.KanComplex ((((middle K I J cof fib).obj F).obj Y).obj k) := by
  have := fibrantTarget_isFibrant fib Y
  exact cosimplicialHom_kanComplex _
    (FrameOverFunctor.commonObj_cofibrant cof (cosimplicialResolutionFamily cof)
      (EvaluatedFrame.originalEvaluation K) (EvaluatedFrame.frame K I J)
      (EvaluatedFrame.augmentation K I J) (F.unop, k.unop))
    (FrameOverFunctor.commonObj_homotopicallyConstant cof (cosimplicialResolutionFamily cof)
      (EvaluatedFrame.originalEvaluation K) (EvaluatedFrame.frame K I J)
      (EvaluatedFrame.augmentation K I J) (EvaluatedFrame.augmentation_weakEquivalence K I J)
      (F.unop, k.unop)) _

variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)

include hcof in
lemma left_weakEquivalence (F : (K ⥤ C)ᵒᵖ) (Y : C) (k : Kᵒᵖ) :
    weakEquivalences SSet.{v} ((((left K I J cof fib).app F).app Y).app k) := by
  have := fibrantTarget_isFibrant fib Y
  exact FrameOverFunctor.homLeft_weakEquivalence cof (cosimplicialResolutionFamily cof)
    (EvaluatedFrame.originalEvaluation K) (EvaluatedFrame.frame K I J)
    (EvaluatedFrame.augmentation K I J) hcof (EvaluatedFrame.augmentation_weakEquivalence K I J)
    (Opposite.op (F.unop, k.unop)) ((fibrantTarget fib).obj Y)

include hcof in
lemma right_weakEquivalence (F : (K ⥤ C)ᵒᵖ) (Y : C) (k : Kᵒᵖ) :
    weakEquivalences SSet.{v} ((((right K I J cof fib).app F).app Y).app k) := by
  have := fibrantTarget_isFibrant fib Y
  exact FrameOverFunctor.homRight_weakEquivalence cof (cosimplicialResolutionFamily cof)
    (EvaluatedFrame.originalEvaluation K) (EvaluatedFrame.frame K I J)
    (EvaluatedFrame.augmentation K I J) hcof (EvaluatedFrame.reedyCofibrant K I J)
    (Opposite.op (F.unop, k.unop)) ((fibrantTarget fib).obj Y)

include hcof in
lemma pointwiseLeft_weakEquivalence (F : (K ⥤ C)ᵒᵖ) (Y : C) (k : Kᵒᵖ) :
    weakEquivalences SSet.{v} ((((pointwiseLeft K I J cof fib).app F).app Y).app k) := by
  exact (weakEquivalences SSet.{v}).comp_mem _ _
    ((weakEquivalences SSet.{v}).of_isIso ((((pointwiseRMapIso K cof fib).inv.app F).app Y).app k))
    (left_weakEquivalence K I J cof fib hcof F Y k)

end SerrePositivity.DiagramModel.PointwiseMappingComparison
