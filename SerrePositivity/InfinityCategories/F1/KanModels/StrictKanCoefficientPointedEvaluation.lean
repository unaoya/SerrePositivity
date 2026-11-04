module
public import SerrePositivity.InfinityCategories.F1.KanModels.StrictKanPointedComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.WeightedConstantSimplex

/-! # strict Kan 比較の元の係数上の pointed map は標準の coherent Hom 比較 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration

/-- 同じ strict Kan 比較の係数作用を、既存の標準 coherent Hom 比較で回収する。 -/
theorem strictKanUnstraighteningComparison_constant_pointed {I : Type u} [Category.{u} I]
    (F : I ⥤ KanObject.{u}) (i : I) :
    (SSet.uliftFunctor.{u + 1, u}).map
      (weightedNerveConstantLift
        (HomotopyLimits.simplicialHomDiagram F pointKanObject ⋙ SSet.opFunctor) i) ≫
      strictKanUnstraighteningComparison F ≫
        pullback.fst pointedSpaceProjection (kanDiagramCoherentNerve F) =
    HomotopyLimits.coherentCosliceFiberComparison pointKanObject (F.obj i) ≫
      vertexFiberι (sliceUnderProjection
        (yonedaEquiv.symm (coherentNerveVertex pointKanObject)))
          (coherentNerveVertex (F.obj i)) ≫ strictKanPointedApexIso.hom := by
  rw [strictKanUnstraighteningComparison_pointed, ← Category.assoc]
  change HomotopyLimits.weightedConstantCosliceMap F pointKanObject i ≫
    strictKanPointedApexIso.hom = _
  rw [← HomotopyLimits.weightedConstantCosliceFiberMap_eq F pointKanObject i]
  rfl

end SerrePositivity.KST.Fibration
