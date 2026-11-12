module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FiberCofiberComparisonProjection
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.StandardCofiberPullback
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PushoutComparison

/-! # 標準 fiber 正方形の押し出し性

概要：標準 fiber 正方形は全複体の dg nerve と Semifree の内部で押し出しでもある。
方針：明示的比較のホモトピー同値性を coslice に反映し、標準 cofiber の余極限性を移す。
規約：安定性は仮定しない。使われ方：D7 の fiber/cofiber の一致。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial
variable {S : Type u} [CommRing S] {B C D : _root_.SerrePositivity.DifferentialGraded.Complex S}

/-- 標準 cofiber から元の fiber 余錐への実際の coslice 比較辺は可逆。 -/
lemma fiberCofiberComparisonSliceEdge_invertible (g : B ⟶ D) (h : C ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberSquare
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackProjectionB g h) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackProjectionC g h))))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fiberCofiberComparisonSliceEdge g h) := by
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fiberCofiberDesc g h)).toTruncated := by
    apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complex_edge_invertible_of_homotopyEquivalence
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derived_edgeChainMap_complexEdge]
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fiberCofiberDesc_homotopyEquivalence g h
  have hp := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fiberCofiberComparisonSliceEdge_projection g h)).mpr he
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.leftFibration_reflects_invertibleEdge
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberSquare
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackProjectionB g h) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackProjectionC g h))))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fiberCofiberComparisonSliceEdge g h) hp

/-- 標準 fiber 正方形は複体の dg nerve の押し出しでもある。 -/
lemma standardFiberSquare_isPushout (g : B ⟶ D) (h : C ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberSquare g h) := by
  have := fiberCofiberComparisonSliceEdge_invertible g h
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fiberCofiberTargetCocone g h) :=
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.standardCofiberCocone_isColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackProjectionB g h)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackProjectionC g h)).of_vertexIso
        (asIso (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fiberCofiberComparisonSliceEdge g h)))
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.rebaseCocone_isColimit_iff (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fiberCofiberComparison_span g h)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberSquare g h))).mp hc

/-- 標準 fiber の四頂点が充満 dg 部分圏に属せば、そこで押し出しでもある。 -/
lemma fullFiberSquare_isPushout (P : _root_.SerrePositivity.DifferentialGraded.Complex S → Prop) (g : B ⟶ D) (h : C ⟶ D)
    (hB : P B) (hC : P C) (hD : P D) (hP : P (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullbackFiber g h)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fullFiberSquare P g h hB hC hD hP) := by
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.isPushoutSquare_of_fullInclusion P
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fullFiberSquare_inclusion]
  exact standardFiberSquare_isPushout g h

/-- Semifree 内の標準 fiber 正方形は押し出しでもある。 -/
lemma semifreeFiberSquare_isPushout (g : B ⟶ D) (h : C ⟶ D)
    (hB : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S B) (hC : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S C) (hD : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeFiberSquare g h hB hC hD) :=
  fullFiberSquare_isPushout (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S) g h hB hC hD
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexSemifree_biprodFiber S (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fiberDifference g h) hB hC hD)

/-- 任意の D(S) の cospan から作った標準 fiber 引き戻しは押し出しでもある。 -/
lemma derivedCospanFiberSquare_isPushout
    (p : (SSet.horn 2 2 : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedCospanFiberSquare p) :=
  semifreeFiberSquare_isPushout _ _ _ _ _

end SerrePositivity.InfinityCategories.Project.DerivedCategories
