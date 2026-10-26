module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PiCriterion.TotalPiCriterion
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PiCriterion.PairPathEquality
public import SerrePositivity.InfinityCategories.F2.Compact.CoconeLegComposition

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
namespace SerrePositivity.InfinityCategories.F2.PiCriterion
open KST.Spectra
variable {B : SSet.{u}}
  (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) (c : JoinCocone F)

/-- 全空間比較を表す、元の図式下の余錐全体の同じ辺。 -/
def nativeTotalComparisonEdge : SSet.Truncated.Edge
    (X := (truncation 2).obj (sliceUnder F)) (coherentDiagramTotalCocone F) c :=
  Classical.choose (homotopyCategory_homMk_surjective (X := sliceUnder F)
    (coherentDiagramTotalCocone F) c (totalCoconeComparison F c))

lemma nativeTotalComparisonEdge_homMk :
    SSet.Truncated.HomotopyCategory.homMk (nativeTotalComparisonEdge F c) =
      totalCoconeComparison F c :=
  Classical.choose_spec (homotopyCategory_homMk_surjective (X := sliceUnder F)
    (coherentDiagramTotalCocone F) c (totalCoconeComparison F c))

/-- 元の余錐比較辺の頂点射影を読み戻した Kan 射。 -/
def nativeTotalValueComparison :
    spaceInfinityObject (coherentDiagramTotalCocone F).vertex ⟶
      spaceInfinityObject c.vertex :=
  spaceInfinityEdgeValue (Compact.coconeVertexEdge (nativeTotalComparisonEdge F c))

lemma nativeTotalComparisonApex_homMk :
    SSet.Truncated.HomotopyCategory.homMk
        (Compact.coconeVertexEdge (nativeTotalComparisonEdge F c)).toTruncated =
      totalVertexComparison F c := by
  change (hoFunctor.map (sliceUnderProjection F)).toFunctor.map
      (SSet.Truncated.HomotopyCategory.homMk (nativeTotalComparisonEdge F c)) = _
  rw [nativeTotalComparisonEdge_homMk]
  rfl

/-- 元の各脚は、同じ余錐辺の頂点比較との合成にホモトピック。 -/
def nativeTotalComparison_leg_homotopy
    (b : ((SSet.uliftFunctor.{u + 1, u}).obj B) _⦋0⦌) :
    Homotopy (spaceInfinityEdgeValue (Compact.coconeTransportLeg c b))
      (spaceInfinityEdgeValue (Compact.coconeTransportLeg (coherentDiagramTotalCocone F) b) ≫
        nativeTotalValueComparison F c) :=
  Compact.coconeLegCompositionHomotopy (nativeTotalComparisonEdge F c) b

/-- 同じ余錐比較の脚の三角形は、零次数で必要な実際の可換式を与える。 -/
lemma nativeTotalComparison_leg_components
    (b : ((SSet.uliftFunctor.{u + 1, u}).obj B) _⦋0⦌)
    (y : (spaceInfinityObject (F.app (Opposite.op ⦋0⦌) b)).obj _⦋0⦌) :
    π₀.mk ((nativeTotalValueComparison F c).app _
        ((spaceInfinityEdgeValue
          (Compact.coconeTransportLeg (coherentDiagramTotalCocone F) b)).app _ y)) =
      π₀.mk ((spaceInfinityEdgeValue (Compact.coconeTransportLeg c b)).app _ y) :=
  (π₀.sound (simplicialHomotopyVertexEdge (nativeTotalComparison_leg_homotopy F c b) y)).symm

/-- 同じ元の脚が二つの類を同一視する条件は、全空間比較との合成でも同じ。 -/
lemma nativeTotalComparison_leg_equality_iff
    (b : ((SSet.uliftFunctor.{u + 1, u}).obj B) _⦋0⦌) (n : ℕ)
    (y : (spaceInfinityObject (F.app (Opposite.op ⦋0⦌) b)).obj _⦋0⦌)
    (a a' : KanHomotopyGroup
      (spaceInfinityObject (F.app (Opposite.op ⦋0⦌) b)).obj n y) :
    KanHomotopyGroup.map (spaceInfinityEdgeValue (Compact.coconeTransportLeg c b)) rfl a =
        KanHomotopyGroup.map (spaceInfinityEdgeValue (Compact.coconeTransportLeg c b)) rfl a' ↔
      KanHomotopyGroup.map
          (spaceInfinityEdgeValue (Compact.coconeTransportLeg (coherentDiagramTotalCocone F) b) ≫
            nativeTotalValueComparison F c) rfl a =
        KanHomotopyGroup.map
          (spaceInfinityEdgeValue (Compact.coconeTransportLeg (coherentDiagramTotalCocone F) b) ≫
            nativeTotalValueComparison F c) rfl a' :=
  homotopy_map_equality_iff (nativeTotalComparison_leg_homotopy F c b) n y a a'

/-- 実際の余錐辺から取った比較の全基点 π 判定でも、元の余極限性を判定できる。 -/
lemma isColimitCone_iff_nativeTotalPiCriterion :
    IsColimitCone c ↔ KanMapPiCriterion (nativeTotalValueComparison F c) := by
  unfold nativeTotalValueComparison
  rw [← spaceEdge_invertible_iff_piCriterion]
  change IsColimitCone c ↔ IsIso (SSet.Truncated.HomotopyCategory.homMk
    (Compact.coconeVertexEdge (nativeTotalComparisonEdge F c)).toTruncated)
  rw [nativeTotalComparisonApex_homMk]
  exact isColimitCone_iff_totalVertexComparison_isIso F c

end SerrePositivity.InfinityCategories.F2.PiCriterion
