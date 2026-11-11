module

public import SerrePositivity.HomotopicalAlgebra.Diagram.WeightedHomotopyColimitFrame
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameOverObject
public import SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftWeakEquivalence

/-! # A target-natural comparison from RMap of hocolim to weighted holim

For each fixed diagram D, the actual comparison is a zigzag
RMap(hocolim D,-) → middle ← frame-Hom ≅ weighted-Hom → holim.
All terms use the same specified fibrant target replacement. The universe
lifts are actual functors, with weak equivalence on every leg proved.
Naturality in the source diagram and comparison of the pointwise input
with independently specified RMap resolutions remain separate steps.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy SerrePositivity.HomotopyFunctionComplex

namespace SerrePositivity.DiagramModel.HocolimMappingComparison
variable (K : Type w) [SmallCategory K] {C : Type u} [Category.{v} C]
  [ModelCategory C] [IsLocallyPresentable.{w} C]
  (I J : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]
  [ModelCategory SSet.{w}]
  (IS JS : MorphismProperty SSet.{w}) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} IS JS]
  (D : K ⥤ C)
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))

abbrev middle : C ⥤ SSet.{v} := fibrantTarget fib ⋙ FrameOverObject.middle cof
  (cosimplicialResolutionFamily cof) ((HomotopyColimit.functor K I J).obj D)
  (WeightedHomotopyColimitFrame.frame K I J IS JS D)
  (WeightedHomotopyColimitFrame.augmentation K I J IS JS D)

abbrev fromRMap : (chosenResolutionHom cof fib).obj
    (Opposite.op ((HomotopyColimit.functor K I J).obj D)) ⟶ middle K I J IS JS D cof fib :=
  Functor.whiskerLeft (fibrantTarget fib) (FrameOverObject.left cof
    (cosimplicialResolutionFamily cof) ((HomotopyColimit.functor K I J).obj D)
    (WeightedHomotopyColimitFrame.frame K I J IS JS D)
    (WeightedHomotopyColimitFrame.augmentation K I J IS JS D))

abbrev fromFrame : fibrantTarget fib ⋙
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (WeightedHomotopyColimitFrame.frame K I J IS JS D) ⟶
      middle K I J IS JS D cof fib :=
  Functor.whiskerLeft (fibrantTarget fib) (FrameOverObject.right cof
    (cosimplicialResolutionFamily cof) ((HomotopyColimit.functor K I J).obj D)
    (WeightedHomotopyColimitFrame.frame K I J IS JS D)
    (WeightedHomotopyColimitFrame.augmentation K I J IS JS D))

abbrev liftedFromRMap := Functor.whiskerRight (fromRMap K I J IS JS D cof fib)
  SSet.uliftFunctor.{w,v}
abbrev liftedFromFrame := Functor.whiskerRight (fromFrame K I J IS JS D cof fib)
  SSet.uliftFunctor.{w,v}

/-- This is the middle isomorphism of the actual lifted zigzag. -/
def weightedIso : fibrantTarget fib ⋙
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (WeightedHomotopyColimitFrame.frame K I J IS JS D) ⋙
      SSet.uliftFunctor.{w,v} ≅
    fibrantTarget fib ⋙ FrameWeightedLimit.weightedHom K IS JS
      (WeightedSourceComparison.frames K I J D) ⋙ SSet.uliftFunctor.{v,w} :=
  Functor.isoWhiskerLeft (fibrantTarget fib)
    (WeightedHomotopyColimitFrame.homIso K I J IS JS D)

abbrev toHolim : fibrantTarget fib ⋙ FrameWeightedLimit.weightedHom K IS JS
      (WeightedSourceComparison.frames K I J D) ⟶
    fibrantTarget fib ⋙ FrameWeightedLimit.functor K IS JS
      (WeightedSourceComparison.frames K I J D) :=
  Functor.whiskerLeft (fibrantTarget fib)
    (FrameWeightedLimit.comparison K IS JS (WeightedSourceComparison.frames K I J D))

abbrev liftedToHolim := Functor.whiskerRight (toHolim K I J IS JS D fib)
  SSet.uliftFunctor.{v,w}

variable [ModelCategory SSet.{v}] [ModelCategory SSet.{max v w}]
  (hcof : cofibrations SSet.{w} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{w} = SSet.modelCategoryQuillen.J.{w}.rlp)
  (hw : weakEquivalences SSet.{w} = SimplicialHomotopy.weakEquivalences)
  (hcofV : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfibV : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (hcofM : cofibrations SSet.{max v w} = MorphismProperty.monomorphisms _)
  (hfibM : fibrations SSet.{max v w} = SSet.modelCategoryQuillen.J.{max v w}.rlp)

include hcof hfib hw hcofV hfibV hcofM hfibM in
lemma liftedFromRMap_weakEquivalence (Y : C) : weakEquivalences SSet.{max v w}
    ((liftedFromRMap K I J IS JS D cof fib).app Y) := by
  apply (SimplicialModel.UniverseLift.weakEquivalences_map_iff.{w,v}
    hcofV hfibV hcofM hfibM _).mpr
  have := fibrantTarget_isFibrant fib Y
  exact FrameOverObject.left_weakEquivalence cof (cosimplicialResolutionFamily cof)
    ((HomotopyColimit.functor K I J).obj D)
    (WeightedHomotopyColimitFrame.frame K I J IS JS D)
    (WeightedHomotopyColimitFrame.augmentation K I J IS JS D) hcofV
    (WeightedHomotopyColimitFrame.augmentation_weakEquivalence K I J IS JS D hcof hfib hw)
    ((fibrantTarget fib).obj Y)

include hcof hfib hcofV hfibV hcofM hfibM in
lemma liftedFromFrame_weakEquivalence (Y : C) : weakEquivalences SSet.{max v w}
    ((liftedFromFrame K I J IS JS D cof fib).app Y) := by
  apply (SimplicialModel.UniverseLift.weakEquivalences_map_iff.{w,v}
    hcofV hfibV hcofM hfibM _).mpr
  have := fibrantTarget_isFibrant fib Y
  exact FrameOverObject.right_weakEquivalence cof (cosimplicialResolutionFamily cof)
    ((HomotopyColimit.functor K I J).obj D)
    (WeightedHomotopyColimitFrame.frame K I J IS JS D)
    (WeightedHomotopyColimitFrame.augmentation K I J IS JS D) hcofV
    (WeightedHomotopyColimitFrame.reedyCofibrant K I J IS JS D hcof hfib)
    ((fibrantTarget fib).obj Y)

omit [ModelCategory SSet.{v}] in
include hcof hfib hcofM hfibM in
lemma liftedToHolim_weakEquivalence (Y : C) : weakEquivalences SSet.{max v w}
    ((liftedToHolim K I J IS JS D fib).app Y) := by
  apply (SimplicialModel.UniverseLift.weakEquivalences_map_iff.{v,w}
    hcof hfib hcofM hfibM _).mpr
  exact FrameWeightedLimit.replacedComparison_weakEquivalence K IS JS hcof hfib
    (WeightedSourceComparison.frames K I J D)
    (fun k => EvaluatedFrame.reedyCofibrant K I J (D, k))
    (fun k => EvaluatedFrame.homotopicallyConstant K I J (D, k)) fib Y

end SerrePositivity.DiagramModel.HocolimMappingComparison
