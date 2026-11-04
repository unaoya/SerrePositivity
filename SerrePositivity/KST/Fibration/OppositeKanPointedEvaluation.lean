module
public import SerrePositivity.KST.Fibration.OppositeKanCoefficientComparison
public import SerrePositivity.InfinityCategories.F1.KanModels.StrictKanCoefficientPointedEvaluation

/-! # 反転 Kan 比較の元の係数作用を、同じ逆成分と標準 coherent Hom 比較で計算する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration

/-- 同じ反転 Kan 実比較の pointed 係数作用の厳密な分解式。 -/
theorem oppositeKanUnstraighteningComparison_constant_pointed
    {I : Type u} [Category.{u} I] (F : I ⥤ KanObject.{u}) (i : I) :
    (SSet.uliftFunctor.{u + 1, u}).map
      (weightedNerveConstantLift (F ⋙ kanObjectForget) i) ≫
        oppositeKanUnstraighteningComparison F ≫
          pullback.fst pointedSpaceProjection
            (kanDiagramCoherentNerve (F ⋙ kanObjectOpFunctor)) =
    (SSet.uliftFunctor.{u + 1, u}).map ((oppositePointHomDiagramIso F).inv.app i) ≫
      HomotopyLimits.coherentCosliceFiberComparison pointKanObject
        ((F ⋙ kanObjectOpFunctor).obj i) ≫
        vertexFiberι (sliceUnderProjection
          (yonedaEquiv.symm (coherentNerveVertex pointKanObject)))
            (coherentNerveVertex ((F ⋙ kanObjectOpFunctor).obj i)) ≫
              strictKanPointedApexIso.hom := by
  have h := congrArg
    (fun m => m ≫ pullback.fst pointedSpaceProjection
      (kanDiagramCoherentNerve (F ⋙ kanObjectOpFunctor)))
    (oppositeKanUnstraighteningComparison_constant F i)
  simpa only [Category.assoc,
    strictKanUnstraighteningComparison_constant_pointed] using h

end SerrePositivity.KST.Fibration
