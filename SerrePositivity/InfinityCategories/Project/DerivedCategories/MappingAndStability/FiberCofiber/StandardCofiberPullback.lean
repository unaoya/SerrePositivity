module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FiberCofiber.CofiberFiberComparisonProjection
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.RightFibrationReflection
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.ComplexEdgeCalculus
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FiberCofiber.FullCofiberSquare
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Triangles.StableColimits

/-! # 標準 cofiber 正方形の引き戻し性

概要：標準 cofiber 正方形は全複体の dg nerve で引き戻しであり、充満部分 dg 圏にも反映する。
方針：明示的比較のホモトピー同値性を slice の比較辺の可逆性に移し、標準 fiber の極限性を移送する。
規約：安定性を前提に使わない。使われ方：D7 の fiber/cofiber の一致。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial
variable {S : Type u} [CommRing S]

/-- 複体間のホモトピー同値を表す dg nerve の辺は可逆。 -/
lemma complex_edge_invertible_of_homotopyEquivalence
    {x y : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S)) _⦋0⦌}
    (e : SSet.Truncated.Edge (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.twoTruncation S (Complex S)) x y)
    (he : HomologicalComplex.homotopyEquivalences (ModuleCat.{u} S) (.up ℤ)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeChainMap e)) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e := by
  have hi := (HomologicalComplex.isIso_quotient_map_iff_homotopyEquivalences _).mpr he
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeChainMap_quotient] at hi
  have : IsIso ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.toH0 S (Complex S)).map (SSet.Truncated.HomotopyCategory₂.homMk e)) :=
    isIso_of_reflects_iso _ (_root_.SerrePositivity.DifferentialGraded.complexHomotopyComparison S)
  have : IsIso (SSet.Truncated.HomotopyCategory₂.homMk e) :=
    isIso_of_reflects_iso _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.toH0 S (Complex S))
  change IsIso ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeToPathHomotopyCategory _).map
    (SSet.Truncated.HomotopyCategory₂.homMk e))
  infer_instance

variable {A B C : _root_.SerrePositivity.DifferentialGraded.Complex S}

/-- 標準 cofiber から標準 fiber への実際の slice 比較辺は可逆。 -/
lemma cofiberFiberComparisonSliceEdge_invertible (f : A ⟶ B) (g : A ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberSquare
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.pushoutInclusionB f g) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.pushoutInclusionC f g))))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberFiberComparisonSliceEdge f g) := by
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.complexEdge (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberFiberLift f g)).toTruncated := by
    apply complex_edge_invertible_of_homotopyEquivalence
    rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.derived_edgeChainMap_complexEdge]
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberFiberLift_homotopyEquivalence f g
  have hp := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve S (Complex S))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberFiberComparisonSliceEdge_projection f g)).mpr he
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.derived_rightFibration_reflects_invertibleEdge
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCospan (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberSquare
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.pushoutInclusionB f g) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.pushoutInclusionC f g)))) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberFiberComparisonSliceEdge f g) hp

/-- 標準 cofiber 正方形は複体の dg nerve の引き戻しでもある。 -/
lemma standardCofiberSquare_isPullback (f : A ⟶ B) (g : A ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.standardCofiberSquare f g) := by
  have := cofiberFiberComparisonSliceEdge_invertible f g
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberFiberSourceCone f g) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardFiberCone_isLimit (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.pushoutInclusionB f g) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.pushoutInclusionC f g)).of_vertexIso
      (asIso (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberFiberComparisonSliceEdge f g))).symm
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.rebaseCone_isLimit (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberFiberComparison_cospan f g).symm
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.cofiberFiberSourceCone f g) hc

/-- 標準 cofiber の四頂点が充満 dg 部分圏に属せば、そこで引き戻しでもある。 -/
lemma fullCofiberSquare_isPullback (P : _root_.SerrePositivity.DifferentialGraded.Complex S → Prop) (f : A ⟶ B) (g : A ⟶ C)
    (hA : P A) (hB : P B) (hC : P C) (hP : P (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.pushoutCofiber f g)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fullCofiberSquare P f g hA hB hC hP) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.isPullbackSquare_of_fullInclusion S (Complex S) P
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.fullCofiberSquare_inclusion]
  exact standardCofiberSquare_isPullback f g

/-- Semifree 内の標準 cofiber 正方形は ∞ 引き戻しでもある。 -/
lemma semifreeCofiberSquare_isPullback (f : A ⟶ B) (g : A ⟶ C)
    (hA : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S A) (hB : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S B) (hC : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeCofiberSquare f g hA hB hC) :=
  fullCofiberSquare_isPullback (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree.complexSemifree S) f g hA hB hC
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexSemifree_pushoutCofiber f g hA hB hC)

/-- 任意の D(S) の span から作った標準 cofiber 押し出しは引き戻しでもある。 -/
lemma derivedSpanCofiberSquare_isPullback
    (p : (SSet.horn 2 0 : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSpanCofiberSquare p) :=
  semifreeCofiberSquare_isPullback _ _ _ _ _

end SerrePositivity.InfinityCategories.Project.DerivedCategories
