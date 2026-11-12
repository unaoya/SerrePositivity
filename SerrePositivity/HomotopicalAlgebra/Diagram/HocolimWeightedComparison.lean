module

public import SerrePositivity.HomotopicalAlgebra.Diagram.WeightedFrameHomNaturality
public import SerrePositivity.HomotopicalAlgebra.Diagram.HocolimFrameComparison
public import SerrePositivity.HomotopicalAlgebra.Diagram.HocolimMappingComparison

/-! # The two-variable natural weighted part of the hocolim mapping comparison -/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.HomotopyFunctionComplex

namespace SerrePositivity.DiagramModel.FrameWeightedLimit
variable (K : Type w) [SmallCategory K] {C : Type u} [Category.{v} C]
  [ModelCategory C] [IsLocallyPresentable.{w} C] [ModelCategory SSet.{w}]
  (I J : MorphismProperty SSet.{w}) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]

abbrev family : (K ⥤ SimplexCategory ⥤ C)ᵒᵖ ⥤ C ⥤ SSet.{w} :=
  SmallHomFrameWeights.homFamily K ⋙
    (Functor.whiskeringRight C (Kᵒᵖ ⥤ SSet.{w}) SSet.{w}).obj (HomotopyLimit.functor Kᵒᵖ I J)

abbrev homFamily : (K ⥤ SimplexCategory ⥤ C)ᵒᵖ ⥤ C ⥤ SSet.{w} :=
  SmallHomFrameWeights.weightedHomFamily K (HomotopyCones.weight Kᵒᵖ I J)

def comparisonFamily : homFamily K I J (C := C) ⟶ family K I J where
  app A := comparison K I J A.unop
  naturality A B f := by
    apply NatTrans.ext
    funext Y
    exact (HomotopyCones.comparison Kᵒᵖ I J).naturality
      (((SmallHomFrameWeights.homFamily K).map f).app Y)

end SerrePositivity.DiagramModel.FrameWeightedLimit

namespace SerrePositivity.DiagramModel.HocolimWeightedComparison
variable (K : Type w) [SmallCategory K] {C : Type u} [Category.{v} C]
  [ModelCategory C] [IsLocallyPresentable.{w} C]
  (I J : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]
  [ModelCategory SSet.{w}]
  (IS JS : MorphismProperty SSet.{w}) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} IS JS]
  (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))

abbrev weightedHom : (K ⥤ C)ᵒᵖ ⥤ C ⥤ SSet.{w} :=
  (EvaluatedFrame.family K I J).op ⋙ FrameWeightedLimit.homFamily K IS JS ⋙
    (Functor.whiskeringLeft C C SSet.{w}).obj (fibrantTarget fib)

abbrev holim : (K ⥤ C)ᵒᵖ ⥤ C ⥤ SSet.{w} :=
  (EvaluatedFrame.family K I J).op ⋙ FrameWeightedLimit.family K IS JS ⋙
    (Functor.whiskeringLeft C C SSet.{w}).obj (fibrantTarget fib)

/-- The existing fixed-D isomorphisms form an actual bifunctor isomorphism. -/
def frameHomIso : HocolimFrameComparison.frameHom K I J IS JS fib ⋙
      (Functor.whiskeringRight C SSet.{v} SSet.{max v w}).obj SSet.uliftFunctor.{w,v} ≅
    weightedHom K I J IS JS fib ⋙
      (Functor.whiskeringRight C SSet.{w} SSet.{max v w}).obj SSet.uliftFunctor.{v,w} :=
  Functor.isoWhiskerRight (Functor.isoWhiskerLeft (EvaluatedFrame.family K I J).op
    (SmallHomFrameWeights.standardFrameHomFamilyIso K (HomotopyCones.weight Kᵒᵖ IS JS)))
    ((Functor.whiskeringLeft C C SSet.{max v w}).obj (fibrantTarget fib))

def toHolim : weightedHom K I J IS JS fib ⟶ holim K I J IS JS fib :=
  Functor.whiskerRight (Functor.whiskerLeft (EvaluatedFrame.family K I J).op
    (FrameWeightedLimit.comparisonFamily K IS JS))
    ((Functor.whiskeringLeft C C SSet.{w}).obj (fibrantTarget fib))

variable (hcof : cofibrations SSet.{w} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{w} = SSet.modelCategoryQuillen.J.{w}.rlp)

include hcof hfib in
lemma toHolim_weakEquivalence (D : (K ⥤ C)ᵒᵖ) (Y : C) : weakEquivalences SSet.{w}
    (((toHolim K I J IS JS fib).app D).app Y) :=
  FrameWeightedLimit.replacedComparison_weakEquivalence K IS JS hcof hfib
    ((EvaluatedFrame.family K I J).obj D.unop)
    (fun k => EvaluatedFrame.reedyCofibrant K I J (D.unop, k))
    (fun k => EvaluatedFrame.homotopicallyConstant K I J (D.unop, k)) fib Y

end SerrePositivity.DiagramModel.HocolimWeightedComparison
