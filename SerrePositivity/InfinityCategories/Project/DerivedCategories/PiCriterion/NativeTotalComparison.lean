module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.TotalPiCriterion
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.PairPathEquality
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.CoconeLegComposition

/-!
概要：全空間比較を余錐全体の実際の辺として選び、元の脚との三角形を保つ。
方針：同じ coslice 辺の射影を Kan 射として読み、脚の合成ホモトピーを使う。
規約：頂点だけで比較辺を選び直さない。
使われ方：D の元の脚の群上の等式を全空間比較へ渡す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion
open KST.Spectra
variable {B : SSet.{u}}
  (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F)

/-- 全空間比較を表す、元の図式下の余錐全体の同じ辺。 -/
def nativeTotalComparisonEdge : SSet.Truncated.Edge
    (X := (truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder F)) (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalCocone F) c :=
  Classical.choose (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder F)
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalCocone F) c (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.totalCoconeComparison F c))

lemma nativeTotalComparisonEdge_homMk :
    SSet.Truncated.HomotopyCategory.homMk (nativeTotalComparisonEdge F c) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.totalCoconeComparison F c :=
  Classical.choose_spec (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder F)
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalCocone F) c (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.totalCoconeComparison F c))

/-- 元の余錐比較辺の頂点射影を読み戻した Kan 射。 -/
def nativeTotalValueComparison :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalCocone F).vertex ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject c.vertex :=
  _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.spaceInfinityEdgeValue (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.coconeVertexEdge (nativeTotalComparisonEdge F c))

lemma nativeTotalComparisonApex_homMk :
    SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.coconeVertexEdge (nativeTotalComparisonEdge F c)).toTruncated =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.totalVertexComparison F c := by
  change (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection F)).toFunctor.map
      (SSet.Truncated.HomotopyCategory.homMk (nativeTotalComparisonEdge F c)) = _
  rw [nativeTotalComparisonEdge_homMk]
  rfl

/-- 元の各脚は、同じ余錐辺の頂点比較との合成にホモトピック。 -/
def nativeTotalComparison_leg_homotopy
    (b : ((SSet.uliftFunctor.{u + 1, u}).obj B) _⦋0⦌) :
    Homotopy (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.spaceInfinityEdgeValue (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.coconeTransportLeg c b))
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.spaceInfinityEdgeValue (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.coconeTransportLeg (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalCocone F) b) ≫
        nativeTotalValueComparison F c) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.coconeLegCompositionHomotopy (nativeTotalComparisonEdge F c) b

/-- 同じ余錐比較の脚の三角形は、零次数で必要な実際の可換式を与える。 -/
lemma nativeTotalComparison_leg_components
    (b : ((SSet.uliftFunctor.{u + 1, u}).obj B) _⦋0⦌)
    (y : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject (F.app (Opposite.op ⦋0⦌) b)).obj _⦋0⦌) :
    π₀.mk ((nativeTotalValueComparison F c).app _
        ((_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.spaceInfinityEdgeValue
          (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.coconeTransportLeg (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalCocone F) b)).app _ y)) =
      π₀.mk ((_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.spaceInfinityEdgeValue (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.coconeTransportLeg c b)).app _ y) :=
  (π₀.sound (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (nativeTotalComparison_leg_homotopy F c b) y)).symm

/-- 同じ元の脚が二つの類を同一視する条件は、全空間比較との合成でも同じ。 -/
lemma nativeTotalComparison_leg_equality_iff
    (b : ((SSet.uliftFunctor.{u + 1, u}).obj B) _⦋0⦌) (n : ℕ)
    (y : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject (F.app (Opposite.op ⦋0⦌) b)).obj _⦋0⦌)
    (a a' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject (F.app (Opposite.op ⦋0⦌) b)).obj n y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.spaceInfinityEdgeValue (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.coconeTransportLeg c b)) rfl a =
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.spaceInfinityEdgeValue (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.coconeTransportLeg c b)) rfl a' ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map
          (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.spaceInfinityEdgeValue (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.coconeTransportLeg (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalCocone F) b) ≫
            nativeTotalValueComparison F c) rfl a =
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map
          (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.spaceInfinityEdgeValue (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.coconeTransportLeg (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalCocone F) b) ≫
            nativeTotalValueComparison F c) rfl a' :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.homotopy_map_equality_iff (nativeTotalComparison_leg_homotopy F c b) n y a a'

/-- 実際の余錐辺から取った比較の全基点 π 判定でも、元の余極限性を判定できる。 -/
lemma isColimitCone_iff_nativeTotalPiCriterion :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c ↔ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.KanMapPiCriterion (nativeTotalValueComparison F c) := by
  unfold nativeTotalValueComparison
  rw [← _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.spaceEdge_invertible_iff_piCriterion]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c ↔ IsIso (SSet.Truncated.HomotopyCategory.homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.coconeVertexEdge (nativeTotalComparisonEdge F c)).toTruncated)
  rw [nativeTotalComparisonApex_homMk]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.isColimitCone_iff_totalVertexComparison_isIso F c

end SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion
