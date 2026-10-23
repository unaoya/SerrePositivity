module

public import SerrePositivity.InfinityCategories.F2.Presentable.SigmaPresheafApexTotalComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.FiniteCoherentProductKanComparison

/-!
概要：元の有限極限錐頂点の評価の余極限から、元の全評価余極限の Kan 積へ比較する。
方針：元の頂点同型の Kan 像と、同じ有限表示の sifted 積比較を合成する。
規約：全射影と置換単位を保持し、底の quasicategory 性は要求しない。
使われ方：P_Σ の sifted 閉性の、元の非空有限錐の指定 Kan 比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.HomotopyLimits
variable {B C : SSet.{u}}
  (r : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SigmaPresheafInfinity C)
  {J : Type u} [Finite J] [Nonempty J] {p : nerve (Discrete J) ⟶ C.op}
  (c : JoinCone p) (hc : IsLimitCone c)
local notation "A" => sigmaPresheafVertexEvaluation r (JoinCone.vertex (JoinCone.ulift c))
local notation "G" => sigmaPresheafFiniteEvaluationFamily r (p := p)

/-- 元の頂点評価の余極限模型から、元の各対象での評価余極限の積への指定比較。 -/
def sigmaPresheafFiniteColimitKanComparison :
    let Q := nonemptyFiniteIndexPresentation J
    F2.coherentDiagramTotalKan A ⟶ nonemptyFiniteSSetProduct Q.1
      (fun i ↦ F2.coherentDiagramTotalKan (G (Q.2.symm (ULift.up i)))) :=
  let Q := nonemptyFiniteIndexPresentation J
  sigmaPresheafApexTotalKanComparison r c hc ≫
    finiteCoherentProductTotalKanComparison Q.1 (fun i ↦ G (Q.2.symm (ULift.up i)))

/-- 元の各対象への脚は、同じ頂点比較と元の反復射影の全空間作用の Kan 像の合成。 -/
lemma sigmaPresheafFiniteColimitKanComparison_projection (j : J) :
    let Q := nonemptyFiniteIndexPresentation J
    sigmaPresheafFiniteColimitKanComparison r c hc ≫
      nonemptyFiniteSSetProjection Q.1
        (fun i ↦ F2.coherentDiagramTotalKan (G (Q.2.symm (ULift.up i)))) (Q.2 j).down =
      sigmaPresheafApexTotalKanComparison r c hc ≫ F2.continuousKanReplacement.map
        (finiteCoherentSpaceProductTotalProjection Q.1
          (fun i ↦ G (Q.2.symm (ULift.up i))) (Q.2 j).down) := by
  dsimp only [sigmaPresheafFiniteColimitKanComparison]
  rw [Category.assoc, finiteCoherentProductTotalKanComparison_projection]

/-- sifted な任意の底上で、元の有限錐頂点の指定 Kan 比較はホモトピー同値。 -/
lemma sigmaPresheafFiniteColimitKanComparison_homotopyEquivalence [IsSiftedInfinity B] :
    IsSimplicialHomotopyEquivalence (sigmaPresheafFiniteColimitKanComparison r c hc) := by
  let Q := nonemptyFiniteIndexPresentation J
  have : KanComplex (nonemptyFiniteSSetProduct Q.1
      (fun i ↦ F2.coherentDiagramTotalKan (G (Q.2.symm (ULift.up i))))) :=
    nonemptyFiniteSSetProduct_kanComplex _ _ (fun _ ↦ inferInstance)
  exact (sigmaPresheafApexTotalKanComparison_homotopyEquivalence r c hc).comp
    (finiteCoherentProductTotalKanComparison_homotopyEquivalence _ _)

/-- 元の指定比較は、元の全空間頂点の単位と各脚で厳密に可換。 -/
lemma sigmaPresheafFiniteColimitKanComparison_unit (j : J) :
    let Q := nonemptyFiniteIndexPresentation J
    F2.continuousKanReplacementUnit.app (smallLeftUnstraightening A) ≫
      sigmaPresheafFiniteColimitKanComparison r c hc ≫
        nonemptyFiniteSSetProjection Q.1
          (fun i ↦ F2.coherentDiagramTotalKan (G (Q.2.symm (ULift.up i)))) (Q.2 j).down =
      F2.coherentTransformationTotalMap A (finiteFamilyCoherentProduct G)
        (sigmaPresheafApexComparisonTransformation r c hc) ≫
      finiteCoherentSpaceProductTotalProjection Q.1
        (fun i ↦ G (Q.2.symm (ULift.up i))) (Q.2 j).down ≫
      F2.continuousKanReplacementUnit.app
        (smallLeftUnstraightening (G (Q.2.symm (ULift.up (Q.2 j).down)))) := by
  dsimp only
  rw [sigmaPresheafFiniteColimitKanComparison_projection, ← Category.assoc,
    sigmaPresheafApexTotalKanComparison, coherentTransformationTotalKanMap_unit,
    Category.assoc, ← F2.continuousKanReplacementUnit.naturality]
  rfl

end SerrePositivity.InfinityCategories.HomotopyLimits
