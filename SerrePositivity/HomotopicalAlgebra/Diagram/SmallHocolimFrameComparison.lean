module

public import SerrePositivity.HomotopicalAlgebra.Diagram.HocolimWeightedComparison
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.SmallHomFrameInvariance

/-! # The hocolim mapping comparison entirely in the small-Hom universe

The common universe lift is fully faithful. Its preimage of the proved
natural isomorphism identifies actual small-Hom frame maps with weighted
Hom already in SSet(w); no model on SSet(v) or SSet(max(v,w)) is required.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy SerrePositivity.HomotopyFunctionComplex

namespace SerrePositivity.DiagramModel.SmallHocolimFrameComparison
variable (K : Type w) [SmallCategory K] {C : Type u} [Category.{v} C]
  [ModelCategory C] [IsLocallyPresentable.{w} C]
  (I J : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]
  [ModelCategory SSet.{w}]
  (IS JS : MorphismProperty SSet.{w}) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} IS JS]
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
  (fib : MorphismProperty.FunctorialFactorizationData (trivialCofibrations C) (fibrations C))

abbrev hom (A : (K ⥤ C) ⥤ SimplexCategory ⥤ C) : (K ⥤ C)ᵒᵖ ⥤ C ⥤ SSet.{w} :=
  A.op ⋙ SmallHomComparison.bifunctor ⋙
    (Functor.whiskeringLeft C C SSet.{w}).obj (fibrantTarget fib)

abbrev frameHom := hom K fib (WeightedHomotopyColimitFrame.frameFamily K I J IS JS)
abbrev middle := hom K fib (HocolimFrameComparison.commonFrame K I J IS JS cof)

abbrev left : (HomotopyColimit.functor K I J).op ⋙ SmallHomComparison.chosenHom cof fib ⟶
    middle K I J IS JS cof fib :=
  Functor.whiskerRight (NatTrans.op (FrameOverFunctor.left cof (cosimplicialResolutionFamily cof)
    (HomotopyColimit.functor K I J) (WeightedHomotopyColimitFrame.frameFamily K I J IS JS)
    (WeightedHomotopyColimitFrame.augmentationFamily K I J IS JS)))
    (SmallHomComparison.bifunctor ⋙ (Functor.whiskeringLeft C C SSet.{w}).obj (fibrantTarget fib))

abbrev right : frameHom K I J IS JS fib ⟶ middle K I J IS JS cof fib :=
  Functor.whiskerRight (NatTrans.op (FrameOverFunctor.right cof (cosimplicialResolutionFamily cof)
    (HomotopyColimit.functor K I J) (WeightedHomotopyColimitFrame.frameFamily K I J IS JS)
    (WeightedHomotopyColimitFrame.augmentationFamily K I J IS JS)))
    (SmallHomComparison.bifunctor ⋙ (Functor.whiskeringLeft C C SSet.{w}).obj (fibrantTarget fib))

/-- Descent through full faithfulness is an actual natural isomorphism, not
an inference of weak equivalence from accessibility or objectwise data. -/
def weightedIso : frameHom K I J IS JS fib ≅
    HocolimWeightedComparison.weightedHom K I J IS JS fib := by
  let P := (Functor.whiskeringRight (K ⥤ C)ᵒᵖ (C ⥤ SSet.{w}) (C ⥤ SSet.{max v w})).obj
    ((Functor.whiskeringRight C SSet.{w} SSet.{max v w}).obj SSet.uliftFunctor.{v,w})
  let e := Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft (WeightedHomotopyColimitFrame.frameFamily K I J IS JS).op
      SmallHomComparison.bifunctorLiftIso)
    ((Functor.whiskeringLeft C C SSet.{max v w}).obj (fibrantTarget fib)) ≪≫
      HocolimWeightedComparison.frameHomIso K I J IS JS fib
  exact P.preimageIso e

variable (hcof : cofibrations SSet.{w} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{w} = SSet.modelCategoryQuillen.J.{w}.rlp)
  (hw : weakEquivalences SSet.{w} = SimplicialHomotopy.weakEquivalences)

include hcof hfib hw in
lemma left_weakEquivalence (D : (K ⥤ C)ᵒᵖ) (Y : C) : weakEquivalences SSet.{w}
    (((left K I J IS JS cof fib).app D).app Y) := by
  have := fibrantTarget_isFibrant fib Y
  exact SmallHomComparison.map_frame_weakEquivalence hcof
    ((FrameOverFunctor.left cof (cosimplicialResolutionFamily cof)
      (HomotopyColimit.functor K I J) (WeightedHomotopyColimitFrame.frameFamily K I J IS JS)
      (WeightedHomotopyColimitFrame.augmentationFamily K I J IS JS)).app D.unop)
    (FrameOverFunctor.commonObj_cofibrant cof (cosimplicialResolutionFamily cof)
      (HomotopyColimit.functor K I J) (WeightedHomotopyColimitFrame.frameFamily K I J IS JS)
      (WeightedHomotopyColimitFrame.augmentationFamily K I J IS JS) D.unop)
    ((cosimplicialResolutionFamily cof).cofibrant ((HomotopyColimit.functor K I J).obj D.unop))
    (FrameOverFunctor.left_weakEquivalence cof (cosimplicialResolutionFamily cof)
      (HomotopyColimit.functor K I J) (WeightedHomotopyColimitFrame.frameFamily K I J IS JS)
      (WeightedHomotopyColimitFrame.augmentationFamily K I J IS JS)
      (fun E => WeightedHomotopyColimitFrame.augmentation_weakEquivalence
        K I J IS JS E hcof hfib hw)
      D.unop)
    ((fibrantTarget fib).obj Y)

include hcof hfib in
lemma right_weakEquivalence (D : (K ⥤ C)ᵒᵖ) (Y : C) : weakEquivalences SSet.{w}
    (((right K I J IS JS cof fib).app D).app Y) := by
  have := fibrantTarget_isFibrant fib Y
  exact SmallHomComparison.map_frame_weakEquivalence hcof
    ((FrameOverFunctor.right cof (cosimplicialResolutionFamily cof)
      (HomotopyColimit.functor K I J) (WeightedHomotopyColimitFrame.frameFamily K I J IS JS)
      (WeightedHomotopyColimitFrame.augmentationFamily K I J IS JS)).app D.unop)
    (FrameOverFunctor.commonObj_cofibrant cof (cosimplicialResolutionFamily cof)
      (HomotopyColimit.functor K I J) (WeightedHomotopyColimitFrame.frameFamily K I J IS JS)
      (WeightedHomotopyColimitFrame.augmentationFamily K I J IS JS) D.unop)
    (WeightedHomotopyColimitFrame.reedyCofibrant K I J IS JS D.unop hcof hfib)
    (FrameOverFunctor.right_weakEquivalence cof (cosimplicialResolutionFamily cof)
      (HomotopyColimit.functor K I J) (WeightedHomotopyColimitFrame.frameFamily K I J IS JS)
      (WeightedHomotopyColimitFrame.augmentationFamily K I J IS JS) D.unop)
    ((fibrantTarget fib).obj Y)

end SerrePositivity.DiagramModel.SmallHocolimFrameComparison
