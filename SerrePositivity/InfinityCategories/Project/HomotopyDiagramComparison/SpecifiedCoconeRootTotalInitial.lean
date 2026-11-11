module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialDiagramRestriction
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCoconeRootVerticalStart
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCoconeRootVerticalEnd

/-!
概要：根辺の四つの全族の固定終点と、元の左右の初期 Hom 族との厳密な一致。
方針：元の三角形・四面体への長辺包含と、その初期頂点の座標を保持する。
規約：同じ全パラメータの族。使われ方：三つの比較を一つの初期 Hom 空間へ移す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
attribute [local irreducible] _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitStrictSpanCocone _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitApexSpan
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRootLeg _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanLeftLeg _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRightLeg
variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
  (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (f ≫ (i ≫ p))) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
  (dB : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (i ≫ p)) (dC : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (j ≫ p)) (y : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌)
local notation "q" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (f ≫ (i ≫ p))
local notation "L" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftRootedTriangle hp p c hc dB dC
local notation "R" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootedRightTetrahedron hp p c hc dB dC
local notation "W" => stdSimplex.δ (1 : Fin 3) ≫ L
local notation "V" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.tetrahedronRootEdge ≫ R

/-- 円柱の時間零の元の全族は、指定した y の上に留まる。 -/
lemma specifiedCoconeRootVerticalStartFamily_fixed :
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootVerticalStartFamily hp p c hc dB dC y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection W) ≫ q =
      SSet.const y := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootVerticalStartFamily,
    Category.assoc (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootVerticalFamily hp p c hc dB dC y) _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection W),
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestriction_projection, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootVerticalFamily_fixed]

/-- 円柱の時間一の全族も、同じ指定 y の上に留まる。 -/
lemma specifiedCoconeRootVerticalEndFamily_fixed :
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootVerticalEndFamily hp p c hc dB dC y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection V) ≫ q =
      SSet.const y := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootVerticalEndFamily_projection, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftRootedHomFamily_fixed]

/-- 元の左長辺の全族の終点は、同じ y の上に留まる。 -/
lemma specifiedCoconeLeftRootTotalFamily_fixed :
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftRootTotalFamily hp p c hc dB dC y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection W) ≫ q =
      SSet.const y := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftRootTotalFamily,
    Category.assoc (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftRootedHomFamily hp p c hc dB dC y) _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection W), _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.sliceUnderRestrict_projection,
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftRootedHomFamily_fixed]

/-- 元の右長辺の全族も、同じ y の上に留まる。 -/
lemma specifiedCoconeRightRootTotalFamily_fixed :
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightRootTotalFamily hp p c hc dB dC y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection V) ≫ q =
      SSet.const y := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightRootTotalFamily,
    Category.assoc (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootedHomTetrahedronFamily hp p c hc dB dC y) _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection V), _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.sliceUnderRestrict_projection,
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootedHomTetrahedronFamily_fixed]

/-- 元の左長辺の初期 Hom 族は、元の左三角形の同じ初期 Hom 族そのもの。 -/
lemma specifiedCoconeLeftRootTotalFamily_initial :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialDiagramHomFamily q c W (stdSimplex.δ (1 : Fin 2))
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootClosingLeft_initial hp p c hc dB dC) y
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftRootTotalFamily hp p c hc dB dC y)
        (specifiedCoconeLeftRootTotalFamily_fixed hp p c hc dB dC y) =
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftInitialHomFamily hp p c hc dB dC y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialDiagramHomFamily_restrict q c L (stdSimplex.δ (1 : Fin 3))
    (stdSimplex.δ (1 : Fin 2)) (stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3))
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.triangleLongEdge_sourceVertex (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootClosingLeft_initial hp p c hc dB dC)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftRootedTriangle_initial hp p c hc dB dC) y
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftRootedHomFamily hp p c hc dB dC y)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftRootedHomFamily_fixed hp p c hc dB dC y)

/-- 元の右長辺の初期 Hom 族も、元の四面体からの同じ初期 Hom 族そのもの。 -/
lemma specifiedCoconeRightRootTotalFamily_initial :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialDiagramHomFamily q c V (stdSimplex.δ (1 : Fin 2))
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightCorrectionHomotopy_target_initial hp p c hc dB dC) y
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightRootTotalFamily hp p c hc dB dC y)
        (specifiedCoconeRightRootTotalFamily_fixed hp p c hc dB dC y) =
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootedInitialHomFamily hp p c hc dB dC y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialDiagramHomFamily_restrict q c R _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.tetrahedronRootEdge
    (stdSimplex.δ (1 : Fin 2))
    (stdSimplex.δ (1 : Fin 2) ≫ (stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.δ (3 : Fin 4)))
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.tetrahedronRootEdge_source
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightCorrectionHomotopy_target_initial hp p c hc dB dC)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootedRightTetrahedron_initialVertex hp p c hc dB dC) y
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootedHomTetrahedronFamily hp p c hc dB dC y)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootedHomTetrahedronFamily_fixed hp p c hc dB dC y)

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
