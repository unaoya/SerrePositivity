module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.NerveMixedAction
public import SerrePositivity.HomotopicalAlgebra.Simplicial.NerveMovingParameter

/-! # Actual coherent choices for both centers with the original families retained

Only the original small lift spaces supply fillers. Parameters and the
index may be large; no larger simplicial model structure is used.
-/

@[expose] public section
universe v u w uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.NerveMixedChoices
variable (C : Type u) [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  {D : Type uD} [Category.{vD} D] (H : D ⥤ MixedResolutionCenters.Index C)
  (K : D ⥤ SSet.{v})

def leftSystem (families : ∀ d, K.obj d ⟶ (MixedResolutionCenters.leftChoices C).obj (H.obj d)) :
    NerveMovingParameter.System.{w, v} (NerveMovingParameter.lifted.{w} K)
      (H ⋙ MixedResolutionCenters.leftChoices C) :=
  NerveMovingParameter.extendFamilies _ _
    (fun d => ResolutionArrowDiagram.fillers C hcof (H.obj d).1)
    (fun d => UniverseLift.map.{w, v} (families d))

def rightSystem
    (families : ∀ d, K.obj d ⟶ (MixedResolutionCenters.rightChoices C).obj (H.obj d)) :
    NerveMovingParameter.System.{w, v} (NerveMovingParameter.lifted.{w} K)
      (H ⋙ MixedResolutionCenters.rightChoices C) :=
  NerveMovingParameter.extendFamilies _ _
    (fun d => ResolutionArrowDiagram.fillers Cᵒᵖ hcof (H.obj d).2)
    (fun d => UniverseLift.map.{w, v} (families d))

lemma left_point
    (families : ∀ d, K.obj d ⟶ (MixedResolutionCenters.leftChoices C).obj (H.obj d)) (d : D) :
    NerveSmallFamilies.point K (H ⋙ MixedResolutionCenters.leftChoices C)
      (leftSystem.{v, u, w} C hcof H K families) d = families d := by
  unfold NerveSmallFamilies.point leftSystem
  rw [NerveMovingParameter.extendFamilies_evaluate]
  exact UniverseLift.lower_map _

lemma right_point
    (families : ∀ d, K.obj d ⟶ (MixedResolutionCenters.rightChoices C).obj (H.obj d)) (d : D) :
    NerveSmallFamilies.point K (H ⋙ MixedResolutionCenters.rightChoices C)
      (rightSystem.{v, u, w} C hcof H K families) d = families d := by
  unfold NerveSmallFamilies.point rightSystem
  rw [NerveMovingParameter.extendFamilies_evaluate]
  exact UniverseLift.lower_map _

def selectedLeft : NerveMovingParameter.System.{w, v} (NerveMovingParameter.lifted.{w} K)
    (H ⋙ MixedResolutionCenters.leftChoices C) :=
  leftSystem C hcof H K (fun d => SSet.stdSimplex.isTerminalObj₀.from (K.obj d) ≫
    ResolutionArrowDiagram.selectedPoint C (H.obj d).1)

def selectedRight : NerveMovingParameter.System.{w, v} (NerveMovingParameter.lifted.{w} K)
    (H ⋙ MixedResolutionCenters.rightChoices C) :=
  rightSystem C hcof H K (fun d => SSet.stdSimplex.isTerminalObj₀.from (K.obj d) ≫
    ResolutionArrowDiagram.selectedPoint Cᵒᵖ (H.obj d).2)

def extendLeft (n : ℕ) (old : NerveMovingParameter.LowerSystem
    (NerveMovingParameter.lifted.{w} K) (H ⋙ MixedResolutionCenters.leftChoices C) n) :
    NerveMovingParameter.System.{w, v} (NerveMovingParameter.lifted.{w} K)
      (H ⋙ MixedResolutionCenters.leftChoices C) :=
  NerveMovingParameter.extend _ _
    (fun d => ResolutionArrowDiagram.fillers C hcof (H.obj d).1) n old

def extendRight (n : ℕ) (old : NerveMovingParameter.LowerSystem
    (NerveMovingParameter.lifted.{w} K) (H ⋙ MixedResolutionCenters.rightChoices C) n) :
    NerveMovingParameter.System.{w, v} (NerveMovingParameter.lifted.{w} K)
      (H ⋙ MixedResolutionCenters.rightChoices C) :=
  NerveMovingParameter.extend _ _
    (fun d => ResolutionArrowDiagram.fillers Cᵒᵖ hcof (H.obj d).2) n old

lemma extendLeft_restrict (n : ℕ) (old : NerveMovingParameter.LowerSystem
    (NerveMovingParameter.lifted.{w} K) (H ⋙ MixedResolutionCenters.leftChoices C) n) :
    Functor.whiskerLeft (Reedy.lowerInclusion (NerveCoherentFamily.reedy D) n)
      (extendLeft C hcof H K n old) = old :=
  NerveMovingParameter.extend_restrict _ _ _ n old

lemma extendRight_restrict (n : ℕ) (old : NerveMovingParameter.LowerSystem
    (NerveMovingParameter.lifted.{w} K) (H ⋙ MixedResolutionCenters.rightChoices C) n) :
    Functor.whiskerLeft (Reedy.lowerInclusion (NerveCoherentFamily.reedy D) n)
      (extendRight C hcof H K n old) = old :=
  NerveMovingParameter.extend_restrict _ _ _ n old

end SerrePositivity.HomotopyFunctionComplex.NerveMixedChoices
