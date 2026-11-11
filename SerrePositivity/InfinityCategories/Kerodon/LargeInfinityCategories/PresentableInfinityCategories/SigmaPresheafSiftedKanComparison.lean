module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SigmaPresheafApexTotalComparison
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FiniteCoherentProductKanComparison

/-!
概要：元の有限極限錐頂点の評価の余極限から、元の全評価余極限の Kan 積へ比較する。
方針：元の頂点同型の Kan 像と、同じ有限表示の sifted 積比較を合成する。
規約：全射影と置換単位を保持し、底の quasicategory 性は要求しない。
使われ方：P_Σ の sifted 閉性の、元の非空有限錐の指定 Kan 比較。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
variable {B C : SSet.{u}}
  (r : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.SigmaPresheafInfinity C)
  {J : Type u} [Finite J] [Nonempty J] {p : nerve (Discrete J) ⟶ C.op}
  (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c)
local notation "A" => _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaPresheafVertexEvaluation r (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone.vertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift c))
local notation "G" => _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaPresheafFiniteEvaluationFamily r (p := p)

/-- 元の頂点評価の余極限模型から、元の各対象での評価余極限の積への指定比較。 -/
def sigmaPresheafFiniteColimitKanComparison :
    let Q := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteIndexPresentation J
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKan A ⟶ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteSSetProduct Q.1
      (fun i ↦ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKan (G (Q.2.symm (ULift.up i)))) :=
  let Q := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteIndexPresentation J
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaPresheafApexTotalKanComparison r c hc ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteCoherentProductTotalKanComparison Q.1 (fun i ↦ G (Q.2.symm (ULift.up i)))

/-- 元の各対象への脚は、同じ頂点比較と元の反復射影の全空間作用の Kan 像の合成。 -/
lemma sigmaPresheafFiniteColimitKanComparison_projection (j : J) :
    let Q := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteIndexPresentation J
    sigmaPresheafFiniteColimitKanComparison r c hc ≫
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteSSetProjection Q.1
        (fun i ↦ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKan (G (Q.2.symm (ULift.up i)))) (Q.2 j).down =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaPresheafApexTotalKanComparison r c hc ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentSpaceProductTotalProjection Q.1
          (fun i ↦ G (Q.2.symm (ULift.up i))) (Q.2 j).down) := by
  dsimp only [sigmaPresheafFiniteColimitKanComparison]
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteCoherentProductTotalKanComparison_projection]

/-- sifted な任意の底上で、元の有限錐頂点の指定 Kan 比較はホモトピー同値。 -/
lemma sigmaPresheafFiniteColimitKanComparison_homotopyEquivalence [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.TensorProductsOfInfinityCategories.IsSiftedInfinity B] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (sigmaPresheafFiniteColimitKanComparison r c hc) := by
  let Q := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteIndexPresentation J
  have : KanComplex (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteSSetProduct Q.1
      (fun i ↦ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKan (G (Q.2.symm (ULift.up i))))) :=
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteSSetProduct_kanComplex _ _ (fun _ ↦ inferInstance)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaPresheafApexTotalKanComparison_homotopyEquivalence r c hc).comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteCoherentProductTotalKanComparison_homotopyEquivalence _ _)

/-- 元の指定比較は、元の全空間頂点の単位と各脚で厳密に可換。 -/
lemma sigmaPresheafFiniteColimitKanComparison_unit (j : J) :
    let Q := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteIndexPresentation J
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening A) ≫
      sigmaPresheafFiniteColimitKanComparison r c hc ≫
        _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nonemptyFiniteSSetProjection Q.1
          (fun i ↦ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKan (G (Q.2.symm (ULift.up i)))) (Q.2 j).down =
      _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTransformationTotalMap A (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteFamilyCoherentProduct G)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaPresheafApexComparisonTransformation r c hc) ≫
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.finiteCoherentSpaceProductTotalProjection Q.1
        (fun i ↦ G (Q.2.symm (ULift.up i))) (Q.2 j).down ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening (G (Q.2.symm (ULift.up (Q.2 j).down)))) := by
  dsimp only
  rw [sigmaPresheafFiniteColimitKanComparison_projection, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sigmaPresheafApexTotalKanComparison, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentTransformationTotalKanMap_unit,
    Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.naturality]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
