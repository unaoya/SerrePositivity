module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoreLimit
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpacePiZero
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.NerveCone
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.SimplicialHomotopyEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanDiagramCoherentNerve
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaces
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Edges
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Vertices
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoherentFilteredTotalDetection
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanConeHomotopyDiagonal
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanConeHomotopyTriangles
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanNativeConeLeg
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallLeftUnstraightening
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.ContinuousKanSequence
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoherentTotalObject
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.F1BKanComplexHomotopyClasses
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.ConeHomotopyEdges
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.HomotopyVerticalRestriction
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SiftedInfinity
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FiniteCoherentProductKanComparison
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FiniteCoherentProductNativeCone
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FiniteCoherentProductTotalMap
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FiniteKanProductNative
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.NonemptyFiniteSSetProduct
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic

/-!
概要：元の有限 coherent 積図式の余極限 Kan 模型の native 積錐の全脚。
方針：同じ全錐円柱の両三角形から、全 native 脚を元の射影の Kan 像と照合する。
規約：全因子について元の一単体とホモトピーを保持する。
使われ方：P_Σ の sifted 余極限閉性の全有限積比較。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
variable (n : ℕ) {B : SSet.{u}} [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.IsSiftedInfinity B]
  (F : Fin (n + 1) → ((SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}))

/-- 元の全錐円柱の頂点辺は、元の全有限積比較と同じ全一単体。 -/
lemma finiteSiftedCoherentProductNativeConeHomotopy_apexEdge :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneHomotopyApexEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteSiftedCoherentProductNativeConeHomotopy n F)).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteCoherentTotalComparisonKanMap n F)).edge := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.homotopyVertexEdge_prism (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteSiftedCoherentProductNativeConeHomotopy n F)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl _ _) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteCoherentTotalComparisonApexPrism n F)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteSiftedCoherentProductNativeConeHomotopy_apex n F) (SSet.yonedaEquiv (𝟙 _))
  exact h.trans (SSet.yonedaEquiv_symm_app_id
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteCoherentTotalComparisonKanMap n F)).edge)

/-- 全錐円柱の各底辺は、元の全空間 Kan 模型の恒等辺そのもの。 -/
lemma finiteSiftedCoherentProductNativeConeHomotopy_diagramEdge
    (i : Discrete (ULift.{u} (Fin (n + 1)))) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneHomotopyDiagramEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteSiftedCoherentProductNativeConeHomotopy n F)
      (ULift.up (ComposableArrows.mk₀ i))).edge =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge
          (𝟙 ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteKanProductDiagram n
            (fun i ↦ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKanObject (F i))).obj i))).edge := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.homotopyVertexEdge_constant (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteSiftedCoherentProductNativeConeHomotopy n F)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr _ _) _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteSiftedCoherentProductNativeConeHomotopy_diagram n F)
    (ULift.up (ComposableArrows.mk₀ i))
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coneHomotopyDiagramEdge _ _).edge = _ at h
  have hv := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve_vertex
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteKanProductDiagram n (fun i ↦ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKanObject (F i))) i).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityVertex_eq_coherent _)
  exact h.trans ((congrArg (fun v ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant v 1) hv).trans
    (by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge_id, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one]; rfl))

/-- 元の native 積錐の各脚を、元の全空間 Kan 対象からの射として読み戻す。 -/
def finiteSiftedCoherentProductNativeKanLeg (i : Discrete (ULift.{u} (Fin (n + 1)))) :
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKanObject (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentSpaceProduct n F) ⟶
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteKanProductDiagram n (fun i ↦ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKanObject (F i))).obj i :=
  _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.kanNativeConeLeg (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteSiftedCoherentProductNativeCone n F) _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteSiftedCoherentProductNativeCone_vertex n F) i

/-- 元の全 native 脚は、それぞれ元の反復射影の全空間作用の Kan 像にホモトピック。 -/
lemma finiteSiftedCoherentProductNativeKanLeg_projection
    (i : Discrete (ULift.{u} (Fin (n + 1)))) :
    Nonempty (SSet.Homotopy (finiteSiftedCoherentProductNativeKanLeg n F i)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentSpaceProductTotalProjection n F i.as.down))) := by
  let K := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKanObject (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentSpaceProduct n F)
  let L := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteKanProductObject n (fun i ↦ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKanObject (F i))
  let hc := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteSiftedCoherentProductNativeCone_vertex n F
  let hd := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteKanProductNativeCone_vertex n (fun i ↦ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKanObject (F i))
  let a := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteCoherentTotalComparisonKanMap n F
  let H := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteSiftedCoherentProductNativeConeHomotopy n F
  let low := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.kanConeHomotopyLower H K hc i (𝟙 _)
    (finiteSiftedCoherentProductNativeConeHomotopy_diagramEdge n F i)
  let up := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.kanConeHomotopyUpper H K L hc hd i a
    (finiteSiftedCoherentProductNativeConeHomotopy_apexEdge n F)
  have h := ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_piZero_eq_iff_homotopy _ _).mpr ⟨low⟩).symm.trans
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_piZero_eq_iff_homotopy _ _).mpr ⟨up⟩)
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_piZero_eq_iff_homotopy _ _).mp
  dsimp only [K, L, hc, hd, a] at h
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteKanProductNativeCone_kanLeg] at h
  change SSet.π₀.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex
      (finiteSiftedCoherentProductNativeKanLeg n F i ≫ (𝟙 _ :
        ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteKanProductDiagram n
          (fun i ↦ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKanObject (F i))).obj i).obj ⟶ _))) =
    SSet.π₀.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteCoherentProductTotalKanComparison n F ≫
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteSSetProjection n (fun i ↦ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKan (F i))
        i.as.down)) at h
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteCoherentProductTotalKanComparison_projection] at h
  simpa only [Category.comp_id] using h

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
