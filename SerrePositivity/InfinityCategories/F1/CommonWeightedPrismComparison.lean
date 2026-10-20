module

public import SerrePositivity.InfinityCategories.F1.CommonWeightedHomAction
public import SerrePositivity.InfinityCategories.F1.UnstraighteningSourceFamilyComparison

/-!
概要：weighted 側の同じ prism から、元の全相対 Hom 上の自然同型を回収する。
方針：共通始域上で持ち上げの比較定理を適用し、同じ係数射の前合成同値で降下する。
規約：prism は入力として明示し、その存在はここでは主張しない。
使われ方：weighted 側の prism の構成後に必要な端点正規化と降下を完結する。
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

/-- 同じ始点と底から weighted 側へ至る prism は、元の全 Hom の自然同型を与える。 -/
def oppositeUnstraighteningHomComparisonIsoOfPrism
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
      functorParameterizedPrism (intervalMappingUncurry (kanDiagramOppositeHomInterval F G))) :
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
    (kanDiagramOppositeHomInterval F G) f hf W hstart hw₁ hwp
  have hj : j = r ≫ a := by
    apply Over.OverMorphism.ext
    rfl
  have hs : ((kanDiagramOppositeHomInterval F G ≫ leftUnstraighteningMappingSpaceMap
      (kanDiagramCoherentNerve (F.val ⋙ kanObjectOpFunctor))
      (kanDiagramCoherentNerve (G.val ⋙ kanObjectOpFunctor))) ≫
      relativeFunctorOverPre pG j) =
      oppositeUnstraighteningHomRight F G ≫ relativeFunctorOverPre pG r := by
    rw [hj, relativeFunctorOverPre_comp, ← Category.assoc]
    rfl
  have ht : relativeFunctorCurry f hf =
      oppositeUnstraighteningHomLeft F G ≫ relativeFunctorOverPre pG r := by
    apply relativeFunctorUncurry_injective pG q
    rw [relativeFunctorUncurry_curry]
    exact (oppositeUnstraighteningHomLeft_common_uncurry F G).symm.trans
      (relativeFunctorOverPre_uncurry pG r (oppositeUnstraighteningHomLeft F G)).symm
  exact strictKanCommonWeightedDescendIso F.val pG
    ((eqToIso (congrArg (fun k => SSet.HomotopyCategory.mk (functorVertex k)) hs.symm)) ≪≫
      e ≪≫ eqToIso (congrArg (fun k => SSet.HomotopyCategory.mk (functorVertex k)) ht))

end SerrePositivity.InfinityCategories
