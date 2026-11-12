module

public import SerrePositivity.KST.Spectra.SpectrumCircleComparisonDifferenceAction

/-!
概要：元の評価錐から companion 極限錐への比較の apex 自己射そのものが Sp の同値。
方針：元の loop の符号から元の全 Hom の成分を反転自己射へ同定し、二乗を計算する。
規約：比較射を別の射で置換しない。使われ方：元の評価四角形の極限性への移送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
local instance circleComparisonApexSimplicialCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory
local instance circleComparisonApexHomKan (X Y : OmegaSpectrum.{u}) :
    KanComplex (SimplicialCategory.sHom X Y) := mappingSpace_kanComplex X Y
local instance circleComparisonApexRawHomKan (z : Sp.{u} _⦋0⦌) :
    KanComplex (circleEvaluationPointedHom z).right := by
  change KanComplex (mappingSpace
    (cotensor PointedSimplicialSet.circle (nativeCotensorInput PointedSimplicialSet.circle z).val)
    (nativeCotensorInput PointedSimplicialSet.circle z).val)
  infer_instance

/-- 元の比較自己射の前合成は、元の companion の差を正符号の類へ送る。 -/
lemma circleCompanionConeComparison_native_difference (z : Sp.{u} _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map
      (RawSpectrumMapping.pointedPre (circleCompanionConeComparisonHom z)
        (nativeCotensorInput PointedSimplicialSet.circle z).val.toKanSequence).right
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (RawSpectrumMapping.pointedPre (circleCompanionConeComparisonHom z)
        (nativeCotensorInput PointedSimplicialSet.circle z).val.toKanSequence))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (circleEvaluationCompanionSimplex z))⁻¹) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (circleEvaluationCompanionSimplex z) := by
  apply FundamentalLoop.toHom_injective
  erw [FundamentalLoop.toHom_pointed_map]
  rw [← circleCompanionEdgewise_difference_toHom]
  exact circleCompanionComparisonDifference_action z

/-- 元の比較自己射は、元の指定された評価 loop の類を逆元へ送る。 -/
lemma circleCompanionConeComparison_native_loop (z : Sp.{u} _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map
      (RawSpectrumMapping.pointedPre (circleCompanionConeComparisonHom z)
        (nativeCotensorInput PointedSimplicialSet.circle z).val.toKanSequence).right
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (RawSpectrumMapping.pointedPre (circleCompanionConeComparisonHom z)
        (nativeCotensorInput PointedSimplicialSet.circle z).val.toKanSequence))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (circleEvaluationLoopSimplex z)) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (circleEvaluationLoopSimplex z))⁻¹ := by
  have h := congrArg Inv.inv (circleCompanionConeComparison_native_difference z)
  simp only [map_inv, inv_inv] at h
  rw [circleEvaluationCompanion_loop_class] at h
  exact h

/-- 元の apex 自己射は、元の反転自己射と同じ全 Hom の成分を持つ。 -/
lemma circleCompanionConeComparison_reversal_component (z : Sp.{u} _⦋0⦌) :
    SpectrumMappingAcyclic.component (circleCompanionConeComparisonHom z) =
    SpectrumMappingAcyclic.component
      (circleCotensorReversal (nativeCotensorInput PointedSimplicialSet.circle z).val) := by
  apply (circleCotensorComponentClass_bijective
    (cotensor PointedSimplicialSet.circle (nativeCotensorInput PointedSimplicialSet.circle z).val)
    (nativeCotensorInput PointedSimplicialSet.circle z).val).injective
  have h := circleCotensorComponentClass_pre (circleCompanionConeComparisonHom z)
    (nativeCotensorInput PointedSimplicialSet.circle z).val
    (SpectrumMappingAcyclic.component
      (𝟙 (cotensor PointedSimplicialSet.circle
        (nativeCotensorInput PointedSimplicialSet.circle z).val)))
  rw [SpectrumMappingAcyclic.pre_component, Category.comp_id,
    circleCotensorComponentClass_identity] at h
  rw [circleCotensorReversal_class, circleCotensorComponentClass_identity]
  erw [circleEvaluationLoopSimplex_evaluation] at h ⊢
  rw [h, circleCompanionConeComparison_native_loop]

/-- 元の apex 自己射の二乗は、元の恒等射と同じ成分。 -/
lemma circleCompanionConeComparison_square_component (z : Sp.{u} _⦋0⦌) :
    SpectrumMappingAcyclic.component
      (circleCompanionConeComparisonHom z ≫ circleCompanionConeComparisonHom z) =
    SpectrumMappingAcyclic.component (𝟙 (cotensor PointedSimplicialSet.circle
      (nativeCotensorInput PointedSimplicialSet.circle z).val)) := by
  have h1 := congrArg (mapπ₀ (SpectrumMappingAcyclic.pre (circleCompanionConeComparisonHom z)
    (cotensor PointedSimplicialSet.circle (nativeCotensorInput PointedSimplicialSet.circle z).val)))
      (circleCompanionConeComparison_reversal_component z)
  have h2 := congrArg (mapπ₀ (SpectrumMappingAcyclic.post
    (cotensor PointedSimplicialSet.circle (nativeCotensorInput PointedSimplicialSet.circle z).val)
    (circleCotensorReversal (nativeCotensorInput PointedSimplicialSet.circle z).val)))
      (circleCompanionConeComparison_reversal_component z)
  rw [SpectrumMappingAcyclic.pre_component, SpectrumMappingAcyclic.pre_component] at h1
  rw [SpectrumMappingAcyclic.post_component, SpectrumMappingAcyclic.post_component] at h2
  exact h1.trans (h2.trans (circleCotensorReversal_square_component _))

/-- 元の比較辺の apex の BF 自己射そのものが、Sp の可逆な辺を与える。 -/
lemma circleCompanionConeComparisonHom_isInvertible (z : Sp.{u} _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (circleCompanionConeComparisonHom z)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentNerveEdge_isInvertible_of_enrichedInverse (circleCompanionConeComparisonHom z)
    (circleCompanionConeComparisonHom z)
    (SpectrumMappingAcyclic.vertexIsoOfComponentEq
      (circleCompanionConeComparison_square_component z))
    (SpectrumMappingAcyclic.vertexIsoOfComponentEq
      (circleCompanionConeComparison_square_component z))

end SerrePositivity.KST.Spectra.OmegaSpectrum
