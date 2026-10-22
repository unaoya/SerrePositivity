module
public import SerrePositivity.KST.Fibration.OppositeKanPointedEvaluation
public import SerrePositivity.KST.Fibration.PointedResolutionProjection

/-! # 元の反転 Kan 比較の pointed 係数作用は既存の左解像比較そのもの -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration

/-- 同じ自然同型の逆成分は、既存の左解像が使う係数同型そのもの。 -/
theorem oppositePointHomDiagramIso_inv_app {I : Type u} [Category.{u} I]
    (F : I ⥤ KanObject.{u}) (i : I) :
    (oppositePointHomDiagramIso F).inv.app i = (pointedSpaceLeftCoefficientIso (F.obj i)).hom :=
  rfl

/-- 実際の反転 Kan 比較の係数作用は、同じ左解像比較を pointed space に含めた射。 -/
theorem oppositeKanUnstraighteningComparison_constant_resolution
    {I : Type u} [Category.{u} I] (F : I ⥤ KanObject.{u}) (i : I) :
    (SSet.uliftFunctor.{u + 1, u}).map
      (weightedNerveConstantLift (F ⋙ kanObjectForget) i) ≫
        oppositeKanUnstraighteningComparison F ≫
          pullback.fst pointedSpaceProjection
            (kanDiagramCoherentNerve (F ⋙ kanObjectOpFunctor)) =
    pointedSpaceLeftResolutionComparison (F.obj i) ≫
      vertexFiberι pointedSpaceProjection
        (spaceInfinityVertex (kanObjectOpFunctor.obj (F.obj i))) := by
  rw [oppositeKanUnstraighteningComparison_constant_pointed,
    oppositePointHomDiagramIso_inv_app, pointedSpaceLeftResolutionComparison_ι,
    coherentPointedFiberComparison]
  simp only [Functor.comp_obj, Category.assoc]

end SerrePositivity.KST.Fibration
