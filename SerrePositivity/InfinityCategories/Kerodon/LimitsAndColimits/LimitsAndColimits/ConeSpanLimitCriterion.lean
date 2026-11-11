module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.ConeDerivedFiberComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.RightFibrationContractible

/-!
概要：coherent な錐の極限性を、始点評価の比較 span の同値性で検出する。
方針：終対象なら全ての fiber が可縮なので自明 Kan fibration、逆は導来ファイバーで検出する。
規約：比較するのは全ての底の頂点 x であり、strict な錐だけの判定ではない。
使われ方：HTT 4.2.4.1 の双対、Kerodon 7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の主比較の slice 側の出口。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 概要：極限錐の始点評価の比較 span は全ての底の頂点で自明 Kan fibration。
方針：各 fiber を錐の slice 内の pinched Hom と同定し、終対象の写像空間の可縮性を使う。
規約：添字 K と図式 p に特別な形は要求しない。
使われ方：Kerodon 7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の極限錐の表現可能な比較の必要条件。 -/
lemma coneMappingEvaluation_trivialKanFibration_of_isLimitCone
    {K X : SSet.{u}} [Quasicategory X] {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c)
    (x : X.obj (Opposite.op ⦋0⦌)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.rightFibrationMappingEvaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p) c x) := by
  let r := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.rightFibrationMappingEvaluation r c x) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.vertexFiberMap_rightFibration _ _ _ _ x
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.rightFibration_trivialKanFibration_of_contractible_fibers
  intro d
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.isContractibleKan_of_iso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.rightFibrationMappingEvaluationFiberIso r c x d).symm
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.isContractibleKan_conePinchedHom_of_isLimitCone hc d.val)

/-- 概要：coherent な錐が極限錐であることと、全ての始点評価の比較がホモトピー同値であることは同値。
方針：必要性は全 fiber の可縮性、十分性は実際の導来ファイバーとの同値と A3d を使う。
規約：既存の sHom からの q_x との同定は、この同値判定とは別途必要である。
使われ方：HTT 4.2.4.1 の双対、Kerodon 7.4.1.6（Tag 05QS）、7.5.4.6（Tag 03BB） の主比較の写像空間側の完成形。 -/
lemma isLimitCone_iff_mappingEvaluation_homotopyEquivalence
    {K X : SSet.{u}} [Quasicategory X] {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c ↔ ∀ x : X.obj (Opposite.op ⦋0⦌),
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.rightFibrationMappingEvaluation (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection p) c x) := by
  constructor
  · intro hc x
    have := coneMappingEvaluation_trivialKanFibration_of_isLimitCone c hc x
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration _).isSimplicialHomotopyEquivalence
  · intro h
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.isLimitCone_iff_conePinchedHom_isContractibleKan c).2
    intro d
    let e := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.conePinchedHom_mappingEvaluationDerivedFiberEquivalence d c
    have he := e.isQCatEquivalence.isSimplicialHomotopyEquivalence
    exact he.isContractibleKan_iff.mpr
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.comparisonFiber_isContractibleKan_of_homotopyEquivalence _ (h d.vertex)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.coneVertexFiberPoint d))

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
