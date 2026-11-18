module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares.SpaceHomotopyPushouts

/-!
概要：台で押し出しとなる Kan 複体の指定余錐を、そのまま空間の余極限として使う。
方針：反変 Hom の厳密な極限を、一脚が fibration の cospan の判定へ渡す。
規約：頂点の Kan 性は余錐の型に含め、置換した頂点や脚は選ばない。
使われ方：HTT 4.2.4.1、Kerodon 7.5.4.6（Tag 03BB）、S8 の離散押し出し。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares

local instance (X Y : KanObject.{u}ᵒᵖ) : KanComplex (SimplicialCategory.sHom X Y) :=
  inferInstanceAs (KanComplex (SimplicialCategory.sHom Y.unop X.unop))

/-- 台の押し出し余錐の同じ反変 Hom の比較は、左脚が単射なら同値。
HTT 4.2.4.1、Kerodon 7.5.4.6（Tag 03BB）。右脚の単射性は課さない。 -/
lemma kanPushoutCocone_reflectedComparison
    {F : AsSmall.{u} WalkingSpan ⥤ KanObject.{u}}
    (c : Cocone F) (hc : IsColimit (kanObjectForget.mapCocone c))
    [Mono ((F ⋙ kanObjectForget).map (AsSmall.up.map WalkingSpan.Hom.fst))]
    (X : KanObject.{u}ᵒᵖ) :
    IsSimplicialHomotopyEquivalence
      (reflectedRepresentableComparison (c.op.whisker oppositeSpanIndex) X) := by
  have : ∀ i, KanComplex
      (((oppositeSpanIndex ⋙ simplicialHomDiagram F.op X) ⋙ SSet.opFunctor).obj i) :=
    fun i ↦ inferInstanceAs
      (KanComplex (SimplicialCategory.sHom (F.obj (oppositeSpanIndex.obj i).unop) X.unop).op)
  have hf : Fibration ((oppositeSpanIndex ⋙ simplicialHomDiagram F.op X).map
      (AsSmall.up.map WalkingCospan.Hom.inl)) := by
    change Fibration (((SimplicialCategory.sHomFunctor KanObject.{u}ᵒᵖ).obj
      (Opposite.op X)).map _)
    rw [kanObjectOppositeHomFunctor_eq X.unop]
    change Fibration ((pre ((F ⋙ kanObjectForget).map
      (AsSmall.up.map WalkingSpan.Hom.fst))).app X.unop.obj)
    infer_instance
  have : Fibration (((oppositeSpanIndex ⋙ simplicialHomDiagram F.op X) ⋙
      SSet.opFunctor).map (AsSmall.up.map WalkingCospan.Hom.inl)) :=
    fibration_opFunctor_map _
  have : SSet.opFunctor.{u}.IsEquivalence := SSet.opEquivalence.isEquivalence_functor
  have : Fibration ((simplicialHomDiagram (oppositeSpanIndex ⋙ F.op) X ⋙
      SSet.opFunctor).map (AsSmall.up.map WalkingCospan.Hom.inl)) :=
    inferInstanceAs (Fibration (((oppositeSpanIndex ⋙ simplicialHomDiagram F.op X) ⋙
      SSet.opFunctor).map (AsSmall.up.map WalkingCospan.Hom.inl)))
  have hlim := (kanObjectOppositeHomCone_isLimit_of_forget c hc X).whiskerEquivalence
    oppositeSpanIndexEquivalence
  have : ∀ i, KanComplex
      ((simplicialHomDiagram (oppositeSpanIndex ⋙ F.op) X ⋙ SSet.opFunctor).obj i) :=
    fun i ↦ inferInstanceAs
      (KanComplex (SimplicialCategory.sHom (F.obj (oppositeSpanIndex.obj i).unop) X.unop).op)
  exact bousfieldKanConeComparison_cospan_leftFibration_homotopyEquivalence _ _
    (isLimitOfPreserves SSet.opFunctor hlim)

/-- 台で押し出しとなる同じ Kan 余錐は、左脚が単射なら空間での余極限。
HTT 4.2.4.1、Kerodon 7.5.4.6（Tag 03BB）。頂点と全ての脚を保持する。 -/
lemma kanPushoutCocone_isColimitCone
    {F : AsSmall.{u} WalkingSpan ⥤ KanObject.{u}}
    (c : Cocone F) (hc : IsColimit (kanObjectForget.mapCocone c))
    [Mono ((F ⋙ kanObjectForget).map (AsSmall.up.map WalkingSpan.Hom.fst))] :
    IsColimitCone (strictNativeCocone c) := by
  rw [strictNativeCocone_isColimit_iff,
    strictCoherentCone_isLimit_iff_whisker _ oppositeSpanIndex,
    strictCoherentCone_isLimit_iff_reflectedRepresentableComparison]
  exact kanPushoutCocone_reflectedComparison c hc

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyPullbackAndHomotopyPushoutSquares
