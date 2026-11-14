module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.SpecifiedCoconeBranchComparisons
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.RelativeTriangleFamilies
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.SpecifiedLiftFibreComposition
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.SpecifiedCoconeLeftTransportEdge
public import
  SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.SpecifiedCoconeRightStandardTransportEdge

/-!
概要：指定余錐の実際の右修正二単体に、長辺の全パラメータ族を保つ相対延長を付ける。
方針：比較辺・修正辺・三角形を一つの証明済みデータとして選び、底の右退化を厳密に照合する。
規約：二単体を別の合成へ置き換えず、選んだ同じ二単体を全ての族で使う。
使われ方：元の全 Hom の族の右枝と境界経路の整合性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
  (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (f ≫ (i ≫ p))) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
  (dB : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (i ≫ p)) (dC : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (j ≫ p))

/-- 実際の二枝と右修正の合成三角形を、指定余錐を固定して一緒に保持する。 -/
structure SpecifiedCoconeBranchData where
  left : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (i ≫ p)).Edge dB
    ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpecifiedPathCocone hp p c hc dB dC).restrict i)
  right : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (j ≫ p)).Edge dC
    ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpecifiedPathCocone hp p c hc dB dC).restrict j)
  transport : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (j ≫ p)).Edge dC
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transportedCoconeVertex dC (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRightLeg c hc f (i ≫ p) rfl dB
      g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC)).val
  triangle : SSet.Edge.CompStruct transport
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpecifiedCorrectionCosliceEdge hp p c hc dB dC) right
  left_projection : (left.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (i ≫ p))).edge =
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanLeftLeg c hc f (i ≫ p) rfl dB
      g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC).edge
  right_projection : (right.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (j ≫ p))).edge =
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRightLeg c hc f (i ≫ p) rfl dB
      g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC).edge
  left_raw : left.edge = (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftTransportEdge hp p c hc dB dC).edge
  transport_raw : transport.edge =
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightStandardTransportEdge hp p c hc dB dC).edge
  triangle_projection : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (j ≫ p)).app (Opposite.op ⦋2⦌) triangle.simplex =
    (SSet.Edge.CompStruct.compId (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRightLeg c hc f (i ≫ p) rfl dB
      g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC)).simplex

set_option maxHeartbeats 800000 in
-- 左の厳密な制限と右の修正先を、同じ標準 prism の頂点と同時に照合する。
/-- 標準 prism 自身の二辺と元の修正辺・底の二単体を一緒に保持するデータを構成する。 -/
def specifiedCoconeBranchData : SpecifiedCoconeBranchData hp p c hc dB dC :=
  Classical.choice (by
    let q := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (j ≫ p)
    let e := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRightLeg c hc f (i ≫ p) rfl dB
      g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC
    let v := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.initialFiberVertexAt q dC dC.vertex rfl
    let w := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap p j _).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpecifiedFiberVertex hp p c hc dB dC)
    let k₀ := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightStandardTransportEdge hp p c hc dB dC
    obtain ⟨k, t, hk, ht⟩ := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.exists_compStruct_of_lift_and_fibre_edge q e v
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.transportedCoconeVertex dC e) w k₀
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightStandardTransportEdge_projection hp p c hc dB dC)
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpecifiedCorrectionEdge hp p c hc dB dC)
    let kC : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (j ≫ p)).Edge dC
        ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpecifiedPathCocone hp p c hc dB dC).restrict j) :=
      ⟨k.edge, k.src_eq, k.tgt_eq.trans (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coconeRestrictionFiber_vertex_val j _
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpecifiedFiberVertex hp p c hc dB dC))⟩
    refine ⟨{ left := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftTransportEdge hp p c hc dB dC
              right := kC
              transport := k₀
              triangle := SSet.Edge.CompStruct.mk t.simplex t.d₂ ?_ t.d₁
              left_projection := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftTransportEdge_projection hp p c hc dB dC
              right_projection := hk
              left_raw := rfl
              transport_raw := rfl
              triangle_projection := ht }⟩
    have h₀ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (j ≫ p)).δ 0 t.simplex =
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpecifiedCorrectionEdge hp p c hc dB dC).edge.val :=
      t.d₀.trans (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.fibreEdgeInclusion_raw q _
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpecifiedCorrectionEdge hp p c hc dB dC))
    simpa only [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpecifiedCorrectionCosliceEdge, SSet.Edge.edge,
      SSet.Edge.toTruncated] using h₀)


/-- 指定した修正辺そのものを面に持つ、選んだ実際の三角形の全単体表示。 -/
def specifiedCoconeRightTriangle : (Δ[2] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (j ≫ p) :=
  SSet.yonedaEquiv.symm (specifiedCoconeBranchData hp p c hc dB dC).triangle.simplex

/-- 選んだ右修正三角形の初辺は、元の標準 prism 自身の輸送辺である。 -/
lemma specifiedCoconeRightTriangle_standardFace :
    stdSimplex.δ (2 : Fin 3) ≫ specifiedCoconeRightTriangle hp p c hc dB dC =
      SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightStandardTransportEdge hp p c hc dB dC).edge := by
  rw [specifiedCoconeRightTriangle, stdSimplex.δ_comp_yonedaEquiv_symm,
    (specifiedCoconeBranchData hp p c hc dB dC).triangle.d₂,
    (specifiedCoconeBranchData hp p c hc dB dC).transport_raw]

/-- 右三角形の長辺は、同じデータに保持した右枝の比較辺。 -/
lemma specifiedCoconeRightTriangle_longEdge :
    stdSimplex.δ (1 : Fin 3) ≫ specifiedCoconeRightTriangle hp p c hc dB dC =
      SSet.yonedaEquiv.symm (specifiedCoconeBranchData hp p c hc dB dC).right.edge := by
  rw [specifiedCoconeRightTriangle, stdSimplex.δ_comp_yonedaEquiv_symm]
  exact congrArg SSet.yonedaEquiv.symm
    (specifiedCoconeBranchData hp p c hc dB dC).triangle.d₁

/-- 右三角形の修正面は、元の指定経路自身の辺。 -/
lemma specifiedCoconeRightTriangle_correction :
    stdSimplex.δ (0 : Fin 3) ≫ specifiedCoconeRightTriangle hp p c hc dB dC =
      SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpecifiedCorrectionCosliceEdge hp p c hc dB dC).edge := by
  rw [specifiedCoconeRightTriangle, stdSimplex.δ_comp_yonedaEquiv_symm]
  exact congrArg SSet.yonedaEquiv.symm
    (specifiedCoconeBranchData hp p c hc dB dC).triangle.d₀

/-- 右三角形の底は、元の span の右脚の右退化そのもの。 -/
lemma specifiedCoconeRightTriangle_base :
    specifiedCoconeRightTriangle hp p c hc dB dC ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (j ≫ p) =
      stdSimplex.σ (1 : Fin 2) ≫ SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRightLeg c hc f (i ≫ p) rfl dB
          g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC).edge := by
  rw [specifiedCoconeRightTriangle, SSet.yonedaEquiv_symm_comp,
    (specifiedCoconeBranchData hp p c hc dB dC).triangle_projection,
    SSet.Edge.CompStruct.compId_simplex, stdSimplex.σ_comp_yonedaEquiv_symm]

/-- 右枝の長辺上の全余錐族を、指定した同じ右修正三角形全体へ延長する相対切断。 -/
def specifiedCoconeRightTriangleSection :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (stdSimplex.δ (1 : Fin 3) ≫ specifiedCoconeRightTriangle hp p c hc dB dC) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (specifiedCoconeRightTriangle hp p c hc dB dC) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.relativeDegenerateTriangleSection (specifiedCoconeRightTriangle hp p c hc dB dC)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (j ≫ p)) _ (specifiedCoconeRightTriangle_base hp p c hc dB dC)

/-- 指定右三角形の全パラメータ切断は、長辺の族を厳密に回収する。 -/
lemma specifiedCoconeRightTriangleSection_longEdge :
    specifiedCoconeRightTriangleSection hp p c hc dB dC ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict (specifiedCoconeRightTriangle hp p c hc dB dC)
        (stdSimplex.δ (1 : Fin 3)) = 𝟙 _ :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.relativeDegenerateTriangleSection_longEdge _ _ _ _

/-- 指定右三角形の延長は、可変な余錐の終点も全単体で保つ。 -/
lemma specifiedCoconeRightTriangleSection_projection :
    specifiedCoconeRightTriangleSection hp p c hc dB dC ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (specifiedCoconeRightTriangle hp p c hc dB dC) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection
          (stdSimplex.δ (1 : Fin 3) ≫ specifiedCoconeRightTriangle hp p c hc dB dC) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.relativeDegenerateTriangleSection_projection _ _ _ _

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
