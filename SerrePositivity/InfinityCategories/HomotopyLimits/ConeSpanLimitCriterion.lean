module

public import SerrePositivity.InfinityCategories.HomotopyLimits.ConeDerivedFiberComparison
public import SerrePositivity.InfinityCategories.Core.RightFibrationContractible

/-!
概要：coherent な錐の極限性を、始点評価の比較 span の同値性で検出する。
方針：終対象なら全ての fiber が可縮なので自明 Kan fibration、逆は導来ファイバーで検出する。
規約：比較するのは全ての底の頂点 x であり、strict な錐だけの判定ではない。
使われ方：HTT 4.2.4.1 の双対、Kerodon 7.4.1.6、7.5.4.6 の主比較の slice 側の出口。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 概要：極限錐の始点評価の比較 span は全ての底の頂点で自明 Kan fibration。
方針：各 fiber を錐の slice 内の pinched Hom と同定し、終対象の写像空間の可縮性を使う。
規約：添字 K と図式 p に特別な形は要求しない。
使われ方：Kerodon 7.4.1.6、7.5.4.6 の極限錐の表現可能な比較の必要条件。 -/
lemma coneMappingEvaluation_trivialKanFibration_of_isLimitCone
    {K X : SSet.{u}} [Quasicategory X] {p : K ⟶ X} (c : JoinCone p) (hc : IsLimitCone c)
    (x : X.obj (Opposite.op ⦋0⦌)) :
    TrivialKanFibration (rightFibrationMappingEvaluation (sliceOverProjection p) c x) := by
  let r := sliceOverProjection p
  have : RightFibration (rightFibrationMappingEvaluation r c x) :=
    vertexFiberMap_rightFibration _ _ _ _ x
  apply rightFibration_trivialKanFibration_of_contractible_fibers
  intro d
  exact isContractibleKan_of_iso (rightFibrationMappingEvaluationFiberIso r c x d).symm
    (isContractibleKan_conePinchedHom_of_isLimitCone hc d.val)

/-- 概要：coherent な錐が極限錐であることと、全ての始点評価の比較がホモトピー同値であることは同値。
方針：必要性は全 fiber の可縮性、十分性は実際の導来ファイバーとの同値と A3d を使う。
規約：既存の sHom からの q_x との同定は、この同値判定とは別途必要である。
使われ方：HTT 4.2.4.1 の双対、Kerodon 7.4.1.6、7.5.4.6 の主比較の写像空間側の完成形。 -/
lemma isLimitCone_iff_mappingEvaluation_homotopyEquivalence
    {K X : SSet.{u}} [Quasicategory X] {p : K ⟶ X} (c : JoinCone p) :
    IsLimitCone c ↔ ∀ x : X.obj (Opposite.op ⦋0⦌),
      IsSimplicialHomotopyEquivalence
        (rightFibrationMappingEvaluation (sliceOverProjection p) c x) := by
  constructor
  · intro hc x
    have := coneMappingEvaluation_trivialKanFibration_of_isLimitCone c hc x
    exact (isQCatEquivalence_of_trivialKanFibration _).isSimplicialHomotopyEquivalence
  · intro h
    apply (isLimitCone_iff_conePinchedHom_isContractibleKan c).2
    intro d
    let e := conePinchedHom_mappingEvaluationDerivedFiberEquivalence d c
    have he := e.isQCatEquivalence.isSimplicialHomotopyEquivalence
    exact he.isContractibleKan_iff.mpr
      (comparisonFiber_isContractibleKan_of_homotopyEquivalence _ (h d.vertex)
        (coneVertexFiberPoint d))

end SerrePositivity.InfinityCategories.HomotopyLimits
