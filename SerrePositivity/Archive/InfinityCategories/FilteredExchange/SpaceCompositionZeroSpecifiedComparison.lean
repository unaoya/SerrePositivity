module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SpaceCompositionZeroExtensionPath
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeFixedExtensionHomotopyEdge

/-!
概要：元の全係数実円柱は、既存の同じ始点固定の指定比較を表す。
方針：同じ延長空間の実辺を作り、その可縮性で元の指定同型へ同定する。
規約：比較を単に別の同型の存在へ弱めず、同じ値を証明する。
使われ方：元の指定精密化の作用を既存の全族比較の終点像へ戻す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable (s : SpaceInfinity.{u} _⦋2⦌)
local notation "K" => EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 0))
local notation "A" => spaceSimplexPointedCoefficients s
local notation "M" => coherentSimplexMaximalization s
local notation "b" => fst Δ[2] A ≫ SSet.yonedaEquiv.symm M
local notation "i" => scaffoldFirstVertex 2 ▷ A
local notation "v" => snd Δ[0] A ≫ pointedCoherentFiberComparison K ≫
  vertexFiberι pointedSpaceProjection (coherentNerveVertex K)

/-- 同じ実全係数円柱から作る、元の二延長頂点間の実辺。 -/
def spaceCompositionZeroExtensionEdge :
    (spaceSimplexPointedFamilyExtensionSpace M).Edge
      (spaceSimplexPointedFamilyExtensionVertex M)
      (spaceCompositionTetrahedronZeroExtensionVertex s) :=
  relativeFixedExtensionHomotopyEdge pointedSpaceProjection b i v
    (spaceSimplexPointedFamily_boundary M) (spaceCompositionZeroPointedHomotopy s)
    (spaceSimplexPointedFamily_projection M) (spaceCompositionTetrahedronZeroFamily_projection s)
    (spaceSimplexPointedFamily_firstVertex M) (spaceCompositionTetrahedronZeroFamily_initial s)
    (spaceCompositionZeroPointedHomotopy_projection s)
    (spaceCompositionZeroPointedHomotopy_initial s)

/-- 同じ実円柱の類を元の可縮延長空間の同型として保持する。 -/
def spaceCompositionZeroCylinderIso :
    VertexIso (spaceSimplexPointedFamilyExtensionVertex M)
      (spaceCompositionTetrahedronZeroExtensionVertex s) := by
  have : KanComplex (spaceSimplexPointedFamilyExtensionSpace M) :=
    (spaceSimplexPointedFamilyExtensionSpace_contractible M).kanComplex
  have : IsInvertibleEdge (spaceCompositionZeroExtensionEdge s).toTruncated :=
    isInvertibleEdge_of_hasFinalHornFillers _ (hasFinalHornFillers_of_kanComplex _)
  exact asIso (SSet.Truncated.HomotopyCategory.homMk
    (spaceCompositionZeroExtensionEdge s).toTruncated)

/-- 元の実全係数円柱の同型は既存の同じ指定比較に厳密に等しい。 -/
lemma spaceCompositionZeroCylinderIso_eq_comparison :
    spaceCompositionZeroCylinderIso s = spaceCompositionTetrahedronZeroComparison s :=
  vertexIso_eq_of_contractible (spaceSimplexPointedFamilyExtensionSpace_contractible M) _ _

/-- 既存の指定比較の順方向の射は元の実全係数円柱の辺の類そのもの。 -/
lemma spaceCompositionTetrahedronZeroComparison_hom_eq_cylinder :
    (spaceCompositionTetrahedronZeroComparison s).hom =
      SSet.Truncated.HomotopyCategory.homMk (spaceCompositionZeroExtensionEdge s).toTruncated :=
  (congrArg (fun e ↦ e.hom) (spaceCompositionZeroCylinderIso_eq_comparison s)).symm

end SerrePositivity.InfinityCategories.F2
