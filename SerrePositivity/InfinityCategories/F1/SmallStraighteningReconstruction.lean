module

public import SerrePositivity.InfinityCategories.F1.KanDiagramOppositeComparison
public import SerrePositivity.InfinityCategories.F1.SmallLeftCoherentTransportReconstruction
public import SerrePositivity.InfinityCategories.F1.StraighteningComparisonInvariance

/-!
概要：既存の straightening 候補の小さい unstraightening は元の left fibration を復元する。
方針：係数反転の関手同型で coherent transport の小さい復元比較の標的を移す。
規約：比較は各対象について構成し、自然な単位全体の完成は主張しない。
使われ方：Kerodon Corollary 5.6.0.6、straightening と unstraightening の対象での復元方向。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：元の left fibration から候補の小さい unstraightening への底上の比較射。
方針：coherent transport の復元比較に係数反転の関手同型の比較射を続ける。
規約：射の選択は非計算的。
使われ方：Kerodon Corollary 5.6.0.6、既存の候補による小さい復元。 -/
noncomputable def smallStraighteningReconstruction
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] :
    E ⟶ smallLeftUnstraightening (leftStraighteningCandidate p) :=
  smallLeftCoherentTransportComparison p ≫
    smallLeftUnstraighteningComparisonOfFunctorIso
      (leftStraighteningCandidateCoherentTransportIso p).symm

/-- 概要：候補による小さい復元比較は元の底を厳密に保つ。
方針：二つの比較射の底上の可換式を合成する。
規約：底の射は恒等。
使われ方：Kerodon Remark 5.6.2.5、復元の辺を LF∞ に入れる。 -/
lemma smallStraighteningReconstruction_projection
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] :
    smallStraighteningReconstruction p ≫
      smallLeftUnstraighteningProjection (leftStraighteningCandidate p) = p := by
  rw [smallStraighteningReconstruction, Category.assoc,
    smallLeftUnstraighteningComparisonOfFunctorIso_projection,
    smallLeftCoherentTransportComparison_projection]

/-- 概要：候補による小さい復元の実際の比較射は前合成同値。
方針：coherent transport の復元と係数比較の前合成同値性を合成する。
規約：順方向は構成した底上の射。
使われ方：Kerodon Corollary 5.6.0.6、復元の同値性。 -/
lemma smallStraighteningReconstruction_isPrecompositionEquivalence
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] :
    IsPrecompositionEquivalence (smallStraighteningReconstruction p) :=
  (smallLeftCoherentTransportComparison_isPrecompositionEquivalence p).comp
    (smallLeftUnstraighteningComparisonOfFunctorIso_isPrecompositionEquivalence
      (leftStraighteningCandidateCoherentTransportIso p).symm)

/-- 概要：候補の小さい unstraightening と元の left fibration は LF∞ 内で同型。
方針：底上の復元比較の前合成同値性を可逆な辺へ移す。
規約：これは対象ごとの同型であり、パラメーター付きの自然性は含めない。
使われ方：Kerodon Corollary 5.6.0.6、分類の復元方向を既存の候補で述べる。 -/
noncomputable def smallStraighteningReconstructionVertexIso
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] :
    VertexIso (leftFibrationInfinityVertex p)
      (leftFibrationInfinityVertex
        (smallLeftUnstraighteningProjection (leftStraighteningCandidate p))) :=
  leftFibrationInfinityVertexIsoOfPrecompositionEquivalence p
    (smallLeftUnstraighteningProjection (leftStraighteningCandidate p))
    (smallStraighteningReconstruction p) (smallStraighteningReconstruction_projection p)
    (smallStraighteningReconstruction_isPrecompositionEquivalence p)

/-- 概要：復元した left fibration の straightening 候補は元の候補と関手同型。
方針：小さい復元比較を coherent な straightening 写像で送る。
規約：一般の coherent 図式の復元でなく、候補の像に対する結論。
使われ方：Kerodon Corollary 5.6.0.6、候補の像での反復の整合性。 -/
noncomputable def smallStraighteningReconstructionCandidateIso
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] :
    FunctorIso (leftStraighteningCandidate p)
      (leftStraighteningCandidate
        (smallLeftUnstraighteningProjection (leftStraighteningCandidate p))) :=
  leftStraighteningCandidateIsoOfPrecompositionEquivalence p
    (smallLeftUnstraighteningProjection (leftStraighteningCandidate p))
    (smallStraighteningReconstruction p) (smallStraighteningReconstruction_projection p)
    (smallStraighteningReconstruction_isPrecompositionEquivalence p)

end SerrePositivity.InfinityCategories
