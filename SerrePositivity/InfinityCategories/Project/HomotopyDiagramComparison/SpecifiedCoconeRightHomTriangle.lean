module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCoconeTriangleFamilies
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.PointHomEdgeLift

/-!
概要：指定余錐の全 Hom の族を、元の右修正辺と合成二単体を同時に保持する三角形の族へする。
方針：右比較辺全体へ底の合成族を保って持ち上げ、同じ右三角形の相対切断を合成する。
規約：元の余錐の余極限性も Hom のパラメータの充填性も使わない。
使われ方：右枝の Hom の比較と指定境界経路を共通 end で結ぶ際の三面の整合性。
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
  (dB : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (i ≫ p)) (dC : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (j ≫ p)) (y : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌)

/-- 特定の指定余錐の全 Hom を、底の元の合成族を保って右比較辺全体へ持ち上げた族。 -/
def specifiedCoconeRightFullHomFamily :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpecifiedPathCocone hp p c hc dB dC).vertex y ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeBranchData hp p c hc dB dC).right.edge) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointRestrictionFullEdgeFamily (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (j ≫ p))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict p j) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.sliceUnderRestrict_projection p j)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpecifiedPathCocone hp p c hc dB dC)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeBranchData hp p c hc dB dC).right y

/-- 同じ族を、選んだ実際の三角形の長辺側の表示へ移す。 -/
def specifiedCoconeRightHomLongEdgeFamily :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpecifiedPathCocone hp p c hc dB dC).vertex y ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (stdSimplex.δ (1 : Fin 3) ≫ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightTriangle hp p c hc dB dC) :=
  specifiedCoconeRightFullHomFamily hp p c hc dB dC y ≫
    eqToHom (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightTriangle_longEdge hp p c hc dB dC).symm)

/-- 指定余錐の全 Hom を同じ実際の右二単体全体に延長した、整合した三面を持つ族。 -/
def specifiedCoconeRightHomTriangleFamily :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpecifiedPathCocone hp p c hc dB dC).vertex y ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightTriangle hp p c hc dB dC) :=
  specifiedCoconeRightHomLongEdgeFamily hp p c hc dB dC y ≫
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightTriangleSection hp p c hc dB dC

/-- 全 Hom の三角形族の長辺は、入力した同じ右比較辺の全 Hom の族。 -/
lemma specifiedCoconeRightHomTriangleFamily_longEdge :
    specifiedCoconeRightHomTriangleFamily hp p c hc dB dC y ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightTriangle hp p c hc dB dC)
          (stdSimplex.δ (1 : Fin 3)) =
      specifiedCoconeRightHomLongEdgeFamily hp p c hc dB dC y := by
  rw [specifiedCoconeRightHomTriangleFamily, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightTriangleSection_longEdge, Category.comp_id]

/-- 三角形の全 Hom の族の可変終点は、元の余錐族の右枝への制限そのもの。 -/
lemma specifiedCoconeRightHomTriangleFamily_endpoint :
    specifiedCoconeRightHomTriangleFamily hp p c hc dB dC y ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightTriangle hp p c hc dB dC) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePointHomFamily (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpecifiedPathCocone hp p c hc dB dC) y ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap p j y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (j ≫ p)) y := by
  rw [specifiedCoconeRightHomTriangleFamily, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightTriangleSection_projection, specifiedCoconeRightHomLongEdgeFamily,
    Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.sliceUnder_eqToHom_projection
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightTriangle_longEdge hp p c hc dB dC).symm]
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.pointRestrictionFullEdgeFamily_endpoint (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (j ≫ p)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict p j) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.sliceUnderRestrict_projection p j)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpecifiedPathCocone hp p c hc dB dC)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeBranchData hp p c hc dB dC).right y

/-- 三角形の全 Hom の族の底も、入力した長辺の底を元の右退化で延長した族そのもの。 -/
lemma specifiedCoconeRightHomTriangleFamily_base :
    specifiedCoconeRightHomTriangleFamily hp p c hc dB dC y ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightTriangle hp p c hc dB dC)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (j ≫ p)) =
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.retractedCosliceBaseFamily (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightTriangle hp p c hc dB dC)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (j ≫ p)) (stdSimplex.δ (1 : Fin 3)) (stdSimplex.σ (1 : Fin 2))
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.triangleBase_retraction _ _ _ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightTriangle_base hp p c hc dB dC))
        (specifiedCoconeRightHomLongEdgeFamily hp p c hc dB dC y) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.relativeDegenerateTriangleSection_base
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightTriangle hp p c hc dB dC) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (j ≫ p)) _
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightTriangle_base hp p c hc dB dC)
  have h' := congrArg (fun k ↦ specifiedCoconeRightHomLongEdgeFamily hp p c hc dB dC y ≫ k) h
  simpa only [specifiedCoconeRightHomTriangleFamily, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightTriangleSection,
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.retractedCosliceBaseFamily, Category.assoc] using h'

/-- 三角形の修正面を、元の指定経路の辺上の全 Hom の族として取り出す。 -/
def specifiedCoconeCorrectionFullHomFamily :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpecifiedPathCocone hp p c hc dB dC).vertex y ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpecifiedCorrectionCosliceEdge hp p c hc dB dC).edge) :=
  specifiedCoconeRightHomTriangleFamily hp p c hc dB dC y ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestriction (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightTriangle hp p c hc dB dC)
      (stdSimplex.δ (0 : Fin 3)) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightTriangle_correction hp p c hc dB dC)

/-- 元の指定修正辺上の族は、可変終点で元の全 Hom の族の右制限を厳密に回収する。 -/
lemma specifiedCoconeCorrectionFullHomFamily_endpoint :
    specifiedCoconeCorrectionFullHomFamily hp p c hc dB dC y ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm
          (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpecifiedCorrectionCosliceEdge hp p c hc dB dC).edge) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePointHomFamily (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpecifiedPathCocone hp p c hc dB dC) y ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap p j y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (j ≫ p)) y := by
  rw [specifiedCoconeCorrectionFullHomFamily, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestriction_projection, specifiedCoconeRightHomTriangleFamily_endpoint]

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
