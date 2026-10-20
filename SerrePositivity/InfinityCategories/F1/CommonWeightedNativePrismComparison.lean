module

public import SerrePositivity.InfinityCategories.F1.CommonWeightedHomAction
public import SerrePositivity.InfinityCategories.F1.KanDiagramNativeOppositeHomParameter
public import SerrePositivity.InfinityCategories.F1.UnstraighteningSourceFamilyComparison

/-!
概要：native な左区間に沿う weighted prism から元の全相対 Hom の比較を得る。
方針：同じ始域上で比較を降下し、左右区間の関手同型で元の作用へ戻す。
規約：prism の存在は明示的な入力とし、区間表示の変更と区別する。
使われ方：実際の分類写像の作用の照合に必要な pointed prism の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
open HomotopyLimits

/-- native な左区間上の prism も、元の右区間の実際の作用の自然同型を与える。 -/
def oppositeUnstraighteningHomComparisonIsoOfNativePrism
    {I : Type u} [SmallCategory I] (F G : KanDiagramObject I)
    (W : ((Δ[1] : SSet.{u + 1}) ⊗ (SSet.uliftFunctor.{u + 1, u}).obj (weightedNerve
      (simplicialHomDiagram (strictKanCommonDiagram F.val) edgewisePointKanObject ⋙
        SSet.opFunctor))) ⊗ (SSet.uliftFunctor.{u + 1, u}).obj
          (edgewiseSubdivision (SimplicialCategory.sHom F G)) ⟶ PointedSpaceInfinity.{u})
    (hw₀ : (prismEndpoint 0 _ ▷ _) ≫ W =
      fst _ _ ≫ weightedCoherentConeComparison (strictKanCommonDiagram F.val)
        edgewisePointKanObject ≫ strictKanCommonUnstraighteningOpposite F.val ≫
          pullback.fst pointedSpaceProjection
            (kanDiagramCoherentNerve (F.val ⋙ kanObjectOpFunctor)))
    (hw₁ : (prismEndpoint 1 _ ▷ _) ≫ W =
      strictKanCommonWeightedHomFamily F G ≫ oppositeKanUnstraighteningComparison G.val ≫
        pullback.fst pointedSpaceProjection
          (kanDiagramCoherentNerve (G.val ⋙ kanObjectOpFunctor)))
    (hwp : W ≫ pointedSpaceProjection =
      ((Δ[1] ◁ (SSet.uliftFunctor.{u + 1, u}).map (weightedNerveProjection
        (simplicialHomDiagram (strictKanCommonDiagram F.val) edgewisePointKanObject ⋙
          SSet.opFunctor))) ▷ _) ≫
      functorParameterizedPrism (intervalMappingUncurry (kanDiagramOppositeLeftHomInterval F G))) :
    FunctorIso (oppositeUnstraighteningHomRight F G) (oppositeUnstraighteningHomLeft F G) := by
  let q := (SSet.uliftFunctor.{u + 1, u}).map (weightedNerveProjection
    (simplicialHomDiagram (strictKanCommonDiagram F.val) edgewisePointKanObject ⋙
      SSet.opFunctor))
  let pF := leftUnstraighteningProjection (kanDiagramCoherentNerve (F.val ⋙ kanObjectOpFunctor))
  let pG := leftUnstraighteningProjection (kanDiagramCoherentNerve (G.val ⋙ kanObjectOpFunctor))
  let r := strictKanCommonWeightedOverMap F.val
  let a := oppositeKanUnstraighteningOverMap F
  let i := strictKanCommonWeightedParameterMap F.val ≫ oppositeKanUnstraighteningComparison F.val
  have hi : i ≫ pF = q := by
    dsimp only [i, pF, q]
    rw [Category.assoc, oppositeKanUnstraighteningComparison_projection,
      strictKanCommonWeightedParameterMap_projection]
  let j : Over.mk q ⟶ Over.mk pF := Over.homMk i hi
  let f := strictKanCommonWeightedHomFamily F G ≫ oppositeKanUnstraighteningComparison G.val
  have hf : f ≫ pG = fst _ _ ≫ q := by
    dsimp only [f, pG, q]
    rw [Category.assoc, oppositeKanUnstraighteningComparison_projection,
      strictKanCommonWeightedHomFamily_projection]
  have hstart : (prismEndpoint 0 _ ▷ _) ≫ W =
      fst _ _ ≫ i ≫ pullback.fst pointedSpaceProjection
        (kanDiagramCoherentNerve (F.val ⋙ kanObjectOpFunctor)) := by
    dsimp only [i]
    rw [strictKanCommonWeightedParameterMap_compare, Category.assoc]
    exact hw₀
  let e := unstraighteningSourceFamilyComparisonIso
    (kanDiagramCoherentNerve (F.val ⋙ kanObjectOpFunctor))
    (kanDiagramCoherentNerve (G.val ⋙ kanObjectOpFunctor)) q i hi
    (kanDiagramOppositeLeftHomInterval F G) f hf W hstart hw₁ hwp
  have hj : j = r ≫ a := by
    apply Over.OverMorphism.ext
    rfl
  have hs : ((kanDiagramOppositeLeftHomInterval F G ≫ leftUnstraighteningMappingSpaceMap
      (kanDiagramCoherentNerve (F.val ⋙ kanObjectOpFunctor))
      (kanDiagramCoherentNerve (G.val ⋙ kanObjectOpFunctor))) ≫
      relativeFunctorOverPre pG j) =
      (kanDiagramOppositeLeftHomInterval F G ≫ leftUnstraighteningMappingSpaceMap
        (kanDiagramCoherentNerve (F.val ⋙ kanObjectOpFunctor))
        (kanDiagramCoherentNerve (G.val ⋙ kanObjectOpFunctor)) ≫
        relativeFunctorOverPre pG a) ≫ relativeFunctorOverPre pG r := by
    rw [hj, relativeFunctorOverPre_comp, ← Category.assoc]
    rfl
  have ht : relativeFunctorCurry f hf =
      oppositeUnstraighteningHomLeft F G ≫ relativeFunctorOverPre pG r := by
    apply relativeFunctorUncurry_injective pG q
    rw [relativeFunctorUncurry_curry]
    exact (oppositeUnstraighteningHomLeft_common_uncurry F G).symm.trans
      (relativeFunctorOverPre_uncurry pG r (oppositeUnstraighteningHomLeft F G)).symm
  exact (oppositeUnstraighteningHomRight_nativeIso F G).symm ≪≫
    strictKanCommonWeightedDescendIso F.val pG
    ((eqToIso (congrArg (fun k => SSet.HomotopyCategory.mk (functorVertex k)) hs.symm)) ≪≫
      e ≪≫ eqToIso (congrArg (fun k => SSet.HomotopyCategory.mk (functorVertex k)) ht))

end SerrePositivity.InfinityCategories
