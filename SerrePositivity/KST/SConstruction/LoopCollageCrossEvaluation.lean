module
public import SerrePositivity.KST.SConstruction.EnrichedFunctorCollageCrossMaps
public import SerrePositivity.KST.SConstruction.LoopCollageEvaluation

/-! # 一般の交差射と元の loop 模型の交差射の一致
概要：一般の collage の交差射を、元の点つき射から作った交差射へ厳密に戻す。
方針：写像空間の単位表示を照合し、元の評価の式へ渡す。
規約：元の suspension・loop・随伴をそのまま使う。
使われ方：指定した全対象の交差辺を元の suspension 構造射へ評価する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open Spectra Spectra.PointedMapping
open SerrePositivity.InfinityCategories
open scoped Simplicial
local instance loopCollageCrossEvaluation_pointed_simplicialCategory :
    SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory

/-- 一般の交差射は、元の loop 値の点つき射から作る交差射そのもの。 -/
lemma enrichedFunctorCollageCross_loop (X Y : PointedKanObject.{u})
    (f : X.obj ⟶ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y.obj) :
    enrichedFunctorCollageCross pointedKanLoopEnrichedFunctor
      (show X ⟶ pointedKanLoopObject Y from ObjectProperty.homMk f) =
      loopCollageCrossMap X Y f := by
  change eHomEquiv SSet (show X ⟶ pointedKanLoopObject Y from ObjectProperty.homMk f) =
    (SSet.unitHomEquiv _).symm (pointedHomVertexEquiv X.obj (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y.obj) f)
  apply (SSet.unitHomEquiv _).injective
  change pointedHomVertexEquiv X.obj (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y.obj) f =
    (SSet.unitHomEquiv ((PointedObject.basedHom X.obj (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y.obj)).right))
      ((SSet.unitHomEquiv _).symm (pointedHomVertexEquiv X.obj (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y.obj) f))
  exact (Equiv.apply_symm_apply _ _).symm

/-- 一般の交差射の評価も、同じ元の逆随伴を厳密に回収する。 -/
lemma enrichedFunctorCollageCross_loop_evaluation (X Y : PointedKanObject.{u})
    (f : X.obj ⟶ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y.obj) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor loopCollageEvaluation).map
      (enrichedFunctorCollageCross pointedKanLoopEnrichedFunctor
        (show X ⟶ pointedKanLoopObject Y from ObjectProperty.homMk f)) =
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv X.obj Y.obj).symm f := by
  rw [enrichedFunctorCollageCross_loop]
  exact loopCollageCrossMap_evaluation X Y f

end SerrePositivity.KST.SConstruction
