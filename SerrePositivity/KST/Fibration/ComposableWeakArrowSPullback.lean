module
public import SerrePositivity.KST.Fibration.ComposableWeakArrowReflection
public import SerrePositivity.KST.Fibration.GappedPullback

/-! # 接続した二つの W 辺の全 S_n の厳密な引き戻し -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration

/-- W 辺の元の終点を零単体図式として抽出する完全関手。 -/
def weakArrowTargetDiagram {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    weakArrowModel q ⟶ ambientDiagramModel (Δ[0] : SSet.{u}) B :=
  weakArrowAmbientInclusion q ≫ ambientDiagramRestriction B (stdSimplex.δ (0 : Fin 2))

/-- W 辺の元の始点を零単体図式として抽出する完全関手。 -/
def weakArrowSourceDiagram {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    weakArrowModel q ⟶ ambientDiagramModel (Δ[0] : SSet.{u}) B :=
  weakArrowAmbientInclusion q ≫ ambientDiagramRestriction B (stdSimplex.δ (1 : Fin 2))

/-- 両 W 辺を共有端点上で貼った図式は、全 gapped S_n でも同じ厳密引き戻し。 -/
theorem composableWeakArrow_sConstruction_isPullback {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n : ℕ) :
    IsPullback ((sEndofunctor n).map (composableWeakFirstExact q)).val
      ((sEndofunctor n).map (composableWeakNextExact q)).val
      ((sEndofunctor n).map (weakArrowTargetDiagram q)).val
      ((sEndofunctor n).map (weakArrowSourceDiagram q)).val :=
  sConstruction_isPullback_of_gapped_reflection (composableWeakArrow_isPullback q) n
    (composableWeakArrow_isGapped_iff q)

end SerrePositivity.KST.Fibration
