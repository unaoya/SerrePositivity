module
public import SerrePositivity.InfinityCategories.F1.OppositeKanUnstraightening
public import SerrePositivity.InfinityCategories.F1.WeightedNerveConstantNaturality

/-! # 元の係数の定値包含と、反転 Kan 図式の同じ unstraightening 比較の作用 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration

/-- 元の定値包含は、同じ係数自然同型の逆成分を通して豊穣係数の包含になる。 -/
theorem oppositePointHomWeightedIso_constant {I : Type u} [Category.{u} I]
    (F : I ⥤ KanObject.{u}) (i : I) :
    weightedNerveConstantLift (F ⋙ kanObjectForget) i ≫
      (oppositePointHomWeightedIso F).inv =
    (oppositePointHomDiagramIso F).inv.app i ≫
      weightedNerveConstantLift
        (HomotopyLimits.simplicialHomDiagram (F ⋙ kanObjectOpFunctor) pointKanObject ⋙
          SSet.opFunctor) i :=
  weightedNerveConstantLift_map (oppositePointHomDiagramIso F).inv i

/-- 元の係数の同じ点は、同じ逆成分と strict Kan 比較の合成で送られる。 -/
theorem oppositeKanUnstraighteningComparison_constant {I : Type u} [Category.{u} I]
    (F : I ⥤ KanObject.{u}) (i : I) :
    (SSet.uliftFunctor.{u + 1, u}).map
      (weightedNerveConstantLift (F ⋙ kanObjectForget) i) ≫
        oppositeKanUnstraighteningComparison F =
    (SSet.uliftFunctor.{u + 1, u}).map ((oppositePointHomDiagramIso F).inv.app i) ≫
      (SSet.uliftFunctor.{u + 1, u}).map
        (weightedNerveConstantLift
          (HomotopyLimits.simplicialHomDiagram (F ⋙ kanObjectOpFunctor) pointKanObject ⋙
            SSet.opFunctor) i) ≫
        strictKanUnstraighteningComparison (F ⋙ kanObjectOpFunctor) := by
  rw [oppositeKanUnstraighteningComparison, ← Category.assoc, ← Functor.map_comp,
    oppositePointHomWeightedIso_constant, Functor.map_comp, Category.assoc]

end SerrePositivity.KST.Fibration
