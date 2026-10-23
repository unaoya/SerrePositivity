module

public import SerrePositivity.InfinityCategories.F1.KanModels.KanEnrichedHomInterval
public import SerrePositivity.InfinityCategories.F1.Weighted.NerveEnriched
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.StrictKanCommonWeightedDescent
public import SerrePositivity.InfinityCategories.F1.Universe.RelativeFunctor
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorSquarePost
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorBaseChange
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraighteningMappingSpaceMap

/-!
概要：反転 unstraightening の自然性四角形の両端を、全 Hom の同じ共通パラメーター上に作る。
方針：元の weighted nerve の作用と、実際の反転 coherent 変換の持ち上げを使う。
規約：両端は同じ底上の相対関手空間への射であり、自然性の同型は後続で証明する。
使われ方：全高次の自然性四角形の両境界と実際の普遍持ち上げの接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories
open HomotopyLimits

variable {I : Type u} [SmallCategory I]

/-- 元の反転比較を、その実際の底上の射として記録する。 -/
def oppositeKanUnstraighteningOverMap (F : KanDiagramObject I) :
    Over.mk ((SSet.uliftFunctor.{u + 1, u}).map
      (weightedNerveProjection (F.val ⋙ kanObjectForget))) ⟶
    Over.mk (leftUnstraighteningProjection
      (kanDiagramCoherentNerve (F.val ⋙ kanObjectOpFunctor))) :=
  Over.homMk (oppositeKanUnstraighteningComparison F.val)
    (oppositeKanUnstraighteningComparison_projection F.val)

/-- 元の weighted nerve の全 Hom 作用を、同じ Hom の共通解像上へ制限する。 -/
def kanDiagramCommonWeightedAction (F G : KanDiagramObject I) :
    (SSet.uliftFunctor.{u + 1, u}).obj
      (edgewiseSubdivision (SimplicialCategory.sHom F G)) ⟶
    relativeFunctorSpace
      ((SSet.uliftFunctor.{u + 1, u}).map (weightedNerveProjection (G.val ⋙ kanObjectForget)))
      ((SSet.uliftFunctor.{u + 1, u}).map (weightedNerveProjection (F.val ⋙ kanObjectForget))) :=
  (SSet.uliftFunctor.{u + 1, u}).map (edgewiseRight (SimplicialCategory.sHom F G)) ≫
    (SSet.uliftFunctor.{u + 1, u}).map
      (weightedNerveMappingSpaceMap (F.val ⋙ kanObjectForget) (G.val ⋙ kanObjectForget)) ≫
    (uliftRelativeFunctorIso (weightedNerveProjection (G.val ⋙ kanObjectForget))
      (weightedNerveProjection (F.val ⋙ kanObjectForget))).hom

/-- weighted nerve の作用の後に標的の元の比較を続ける、全パラメーターの左端。 -/
def oppositeUnstraighteningHomLeft (F G : KanDiagramObject I) :
    (SSet.uliftFunctor.{u + 1, u}).obj
      (edgewiseSubdivision (SimplicialCategory.sHom F G)) ⟶
    relativeFunctorSpace
      (leftUnstraighteningProjection (kanDiagramCoherentNerve (G.val ⋙ kanObjectOpFunctor)))
      ((SSet.uliftFunctor.{u + 1, u}).map (weightedNerveProjection (F.val ⋙ kanObjectForget))) :=
  kanDiagramCommonWeightedAction F G ≫ relativeFunctorPost
    ((SSet.uliftFunctor.{u + 1, u}).map (weightedNerveProjection (G.val ⋙ kanObjectForget)))
    (leftUnstraighteningProjection (kanDiagramCoherentNerve (G.val ⋙ kanObjectOpFunctor)))
    (oppositeKanUnstraighteningComparison G.val)
    (oppositeKanUnstraighteningComparison_projection G.val)
    ((SSet.uliftFunctor.{u + 1, u}).map (weightedNerveProjection (F.val ⋙ kanObjectForget)))

/-- 始域の元の比較の後に実際の反転 coherent 変換の作用を続ける、同じ全パラメーターの右端。 -/
def oppositeUnstraighteningHomRight (F G : KanDiagramObject I) :
    (SSet.uliftFunctor.{u + 1, u}).obj
      (edgewiseSubdivision (SimplicialCategory.sHom F G)) ⟶
    relativeFunctorSpace
      (leftUnstraighteningProjection (kanDiagramCoherentNerve (G.val ⋙ kanObjectOpFunctor)))
      ((SSet.uliftFunctor.{u + 1, u}).map (weightedNerveProjection (F.val ⋙ kanObjectForget))) :=
  kanDiagramOppositeHomInterval F G ≫
    leftUnstraighteningMappingSpaceMap (kanDiagramCoherentNerve (F.val ⋙ kanObjectOpFunctor))
      (kanDiagramCoherentNerve (G.val ⋙ kanObjectOpFunctor)) ≫
    relativeFunctorOverPre
      (leftUnstraighteningProjection (kanDiagramCoherentNerve (G.val ⋙ kanObjectOpFunctor)))
      (oppositeKanUnstraighteningOverMap F)

/-- 左端の展開は、元の全 weighted 作用への元の標的比較の後合成そのもの。 -/
lemma oppositeUnstraighteningHomLeft_uncurry (F G : KanDiagramObject I) :
    relativeFunctorUncurry (oppositeUnstraighteningHomLeft F G) =
      relativeFunctorUncurry (kanDiagramCommonWeightedAction F G) ≫
        oppositeKanUnstraighteningComparison G.val :=
  relativeFunctorUncurry_post _ _ _ _ _ _

/-- 右端の展開は、同じ反転変換の実際の unstraightening 作用を元の始域比較で制限した族。 -/
lemma oppositeUnstraighteningHomRight_uncurry (F G : KanDiagramObject I) :
    relativeFunctorUncurry (oppositeUnstraighteningHomRight F G) =
      (oppositeKanUnstraighteningComparison F.val ▷
        (SSet.uliftFunctor.{u + 1, u}).obj
          (edgewiseSubdivision (SimplicialCategory.sHom F G))) ≫
      relativeFunctorUncurry (kanDiagramOppositeHomInterval F G ≫
        leftUnstraighteningMappingSpaceMap
          (kanDiagramCoherentNerve (F.val ⋙ kanObjectOpFunctor))
          (kanDiagramCoherentNerve (G.val ⋙ kanObjectOpFunctor))) := by
  rw [oppositeUnstraighteningHomRight, ← Category.assoc]
  exact relativeFunctorOverPre_uncurry
    (leftUnstraighteningProjection (kanDiagramCoherentNerve (G.val ⋙ kanObjectOpFunctor)))
    (oppositeKanUnstraighteningOverMap F)
    (kanDiagramOppositeHomInterval F G ≫ leftUnstraighteningMappingSpaceMap
      (kanDiagramCoherentNerve (F.val ⋙ kanObjectOpFunctor))
      (kanDiagramCoherentNerve (G.val ⋙ kanObjectOpFunctor)))

end SerrePositivity.InfinityCategories
